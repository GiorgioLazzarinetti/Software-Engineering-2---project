
// SIGNATURES

some sig User{
ID: one UserID,
userCreditCard: one CreditCard,
userPayment: set Payment,
userPosition: one Position,
}

sig Payment{
ID: one PaymentID,
}

sig CreditCard{
}

sig Position{
}

sig UserID{}

sig PaymentID{}

sig Reservation{
user: one User,
car: one Car,
}

sig Car{
position: one Position,
powerGrid: lone PowerGrid,
monitor: one Monitor,
sensor: some Sensor,
status: one Status,
}

abstract sig Status{}

one sig Available extends Status{}

one sig InUse extends Status{}

one sig Rented extends Status{}

one sig Damaged extends Status{}

sig Monitor{}

sig Sensor{}

sig SafeArea{
position: one Position,
}

sig SpecialParkingArea extends SafeArea{
powerGrid: some PowerGrid,
}

sig PowerGrid{}

// FACTS



//each payments must be associated exactly to one user
fact paymentAssociatedToOneUser{
all p: Payment | (some u: User |p in  u.userPayment)
}

//each positions must be associated either to a user or to a car or to a safe area
fact positionAssociated{
all p: Position | (some u: User | p in u.userPosition) || (some c: Car | p in c.position) || (some sa: SafeArea | p in sa.position)
}

//each credit cards must be associated to at least one user
fact creditCardAssociated{
all c: CreditCard | (some u: User |c=u.userCreditCard)
}

//each monitors must be associated to a car
fact monitoAssociated{
all m: Monitor| (some c: Car |m= c.monitor)
}

//each sensors must be associated to a car
fact sensorAssociated{
all s: Sensor| (some c: Car |s in c.sensor)
}

//each UserIDs must be associated to a user 
fact userIDAssociated{
all id: UserID | (some u: User | id=u.ID) 
}

//each paymentIDs must be associated to a payment 
fact paymentIDAssociated{
all id: PaymentID | (some p: Payment | id=p.ID) 
}

//each power grids must be associated to one special parking area
fact powerGridAssociated{
all pg: PowerGrid | (some spa: SpecialParkingArea | pg in spa.powerGrid)
}

//two users cannot refer to the same ID
fact uniqueUserID{
all disj u1, u2: User | u1.ID!=u2.ID
} 

//two payments cannot refer to the same ID
fact uniquePaymentID{
all disj p1, p2: Payment | p1.ID!=p2.ID
}

//two users must have different payments
fact uniqueUserPayment{
all disj u1,u2:User | u1.userPayment&u2.userPayment = none
}

//two cars must be associated to different power grid
fact uniquePowerGrid{
all disj c1, c2: Car | c1.powerGrid!=c2.powerGrid || c1.powerGrid=none
}

//two car cannot be associated to the same monitor
fact uniqueMonitor{
all disj c1,c2:Car | c1.monitor!=c2.monitor 
}

//two cars cannot be associated to the same set of sensors
fact uniqueSensors{
all disj c1, c2: Car | c1.sensor&c2.sensor= none
}

//two users cannot be associated to the same position
fact uniquePositionForDifferentUsers{
all disj u1, u2: User | u1.userPosition!=u2.userPosition
}

//two reservations cannot be associated to the same user and car
fact uniqeuReservation{
all disj r1, r2: Reservation | r1.user!=r2.user 
all disj  r1, r2: Reservation | r1.car!=r2.car
}


//two cars cannot be associated to the same position
fact uniquePositionForDifferentCars{
all disj c1, c2: Car | c1.position!=c2.position
}

//two safe areas cannot be associated to the same position
fact uniquePositionForDifferentSafeAreas{
all disj sa1, sa2: SafeArea | sa1.position!=sa2.position
}

//two special parking areas cannot be associated to the same position
fact uniquePositionForDifferentSpecialParkingAreas{
all disj spa1, spa2: SpecialParkingArea | spa1.position!=spa2.position
}

//two special parking areas cannot be associated to the same power grid
fact uniquePowerGrid{
all disj spa1, spa2 : SpecialParkingArea | spa1.powerGrid&spa2.powerGrid= none
}

//users, cars and safe areas cannot have the same position
fact uniquePosition{
no  u: User, c: Car | u.userPosition=c.position 
no u: User, sa: SafeArea | u.userPosition = sa.position
no c: Car, sa: SafeArea | c.position = sa.position
}

// the status of the car depends from the reservation. if a car is associated to a reservation, it can be in use or rented
// else it must be damaged or available
fact carStatus{
all r: Reservation, c: Car | r.car=c implies (c.status&	InUse!=none || c.status&Rented!=none)
all c: Car|  c not in Reservation.car  implies (c.status&Available!=none || c.status&Damaged!=none)
}


// ASSERTION

assert reservationCheck{
#(Car.status&InUse + Car.status&Rented)=0 implies #(Reservation)=0
}

check reservationCheck

pred show{}

run show for 5 but exactly 3 Car, exactly 1 Reservation








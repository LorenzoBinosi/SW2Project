// ---- SIGNATURES ----

sig Driver
{
		username: one Stringa,
		email: one Stringa,
		password: one Stringa,
		name: one Stringa,
		surname: one Stringa,
		birthday: one Stringa,
		address: one Stringa,
		phonenumber: one Stringa,
		position: lone Position,
		creditcard: one CreditCard,
		drivinglicense: one DrivingLicense,
}

sig Stringa {}

sig Position
{
		latitude: one Int,
		logitude: one Int,
}

sig CreditCard
{
		ccnumber: one Stringa,
		money: one Int,
		expireddate: one Int,
}
{
		expireddate > 0
}

sig DrivingLicense
{
		licenseid: one Int,
		expireddate: one Int,
}
{
		expireddate > 0
}

sig Car
{
		licenseplate: one Int,
		batterylevel: one Int,
		position: one Position,
		carstatus: one CarStatus,
}
{
		batterylevel >= 0
		batterylevel <= 100
		(batterylevel <= 25) implies (carstatus = OutOfService)
}

abstract sig CarStatus {}
one sig Available extends CarStatus {}
one sig Reserved extends CarStatus {}
one sig InUse extends CarStatus {}
one sig OutOfService extends CarStatus {}

sig Rent
{
		reservationdate: one Int,
		begindate: lone Int,
		enddate: lone Int,
		numofpassenger: one Int,
		price: one Int,
		rentstatus: one RentStatus,
}
{
		reservationdate > 0
		reservationdate < begindate
		begindate < enddate
		price > 0
		numofpassenger >= 0
		numofpassenger <= 4
}
		
abstract sig RentStatus {}
one sig InProgress extends RentStatus {}
one sig Completed extends RentStatus {}
one sig ReservationAborted extends RentStatus {}

// ---- FACTS ----

//No drivers with the same username, driving license or email
fact UniqueDriver
{
		no disjoint d1, d2: Driver | (d1.username = d2.username or d1.email = d2.email or d1.drivinglicense.licenseid = d2.drivinglicense.licenseid)
}

//No license without driver
fact LicenseWithoutDriver
{
		all dl: DrivingLicense | one d: Driver | dl in d.drivinglicense
}

//No creditcard without driver
fact LicenseWithoutDriver
{
		all cc: CreditCard | some d: Driver | cc in d.creditcard
}

pred show()
{
		#Driver >= 3
		#CreditCard >= 2
		#Car >= 2
		#Rent >= 5
}

run show for 10

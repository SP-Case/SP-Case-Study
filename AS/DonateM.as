//19 axioms
package DonateM;
import EventM;
{

Spec Donate;
extends AbsData;
	uses Integer;
	Attr
		uid: Integer;
		eid: Integer;
		amount: Integer;
	Axiom
		For all d:Donate that
			d.amount > 0;
		End
End

Spec DonateDB;
	uses Donate;
	Attr
		datas[0..*]:Donate;
End

Spec DonateReturn;
	uses Integer,AbsData,DonateDB;
	Attr
		id: Integer;
		d: AbsData;
		ddb: DonateDB;
End

Spec DEReturn;
	uses DonateReturn,EventReturn;
	Attr
		dre: DonateReturn;
		ere: EventReturn;
End

Spec DonateM;
	uses UtilOp,Account,EventM,Integer,DonateDB,EventDB,UserDB,DEReturn;
	Tran
		donate(Integer,Integer,Integer,DonateDB,EventDB,UserDB):DEReturn;
	Axiom
		For all dm:DonateM, a:Account, em:EventM, util:UtilOp, ui,ei,n:Int, dbd:DonateDB, dbe:EventDB, dbu:UserDB that
			let dere = dm.donate(ui,ei,n,dbd,dbe,dbu) in 
				dere.ure = a.subBalance(ui,n,dbu);
				dere.ere = em.updateEvent(ui,ei,n,dbe), if dere.ure.user <> null;
				util.isin(dere.dre.d, dbd.datas) = false, if dere.ere.e <> null;
				dere.dre.d.uid = ui, if dere.ere.e <> null;
				dere.dre.d.eid = ei, if dere.ere.e <> null;
				dere.dre.d.amount = n, if dere.ere.e <> null;
				dere.dre.ddb.datas = util.union(dbd.datas, dere.dre.d), if dere.ere.e <> null;

				dere.dre.d = null, if dere.ure.user = null;
				dere.ere.e = null, if dere.ure.user = null;
				dere.ere.edb = dbe, if dere.ure.user = null;
				dere.ure.udb = dbu, if dere.ure.user = null;

				dere.dre.d = null, if dere.ere.e = null;
				dere.ere.e = null, if dere.ere.e = null;
				dere.ere.edb = dbe, if dere.ere.e = null;
				dere.ure.udb = dbu, if dere.ere.e = null;
			End
		End

		For dm:DonateM, a:Account, em:EventM, ui,ei,n:Int, dbd:DonateDB, dbe:EventDB, dbu:UserDB that
			let
				u = a.getBalance(ui,dbu)
				ev1 = em.getEvent(ei,dbe)
				dere = dm.donate(ui,ei,n,dbd,dbe,dbu)
				ev2 = em.getEvent(ei,dere.ere.edb)
			in
				ev2.total = ev1.total + n, if ev1.status = true, u.balance >= n;
				ev2.total = ev1.total, if ev1 != null, u.balance < n;
				ev2.total = ev1.total, if ev1.status = false;
			End
		End
End
}

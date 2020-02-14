//44 axioms
package EventM;
import Account;
{

Spec Event;
extends AbsData;
	uses Integer, String, Bool;
	Attr
		uid: Integer;
		des: String;
		target: Integer;
		total: Integer;
		status: Bool;
	Axiom
		For all e:Event that
			e.total >= 0;
			e.target >= 0;
		End
End

Spec EventDB;
	uses Event;
	Attr
		datas[0..*]:Event;
End

Spec EventReturn;
	uses Integer, AbsData, EventDB;
	Attr
		id: Integer
		e: AbsData;
		edb: EventDB;
End

Spec EUReturn;
	uses EventReturn, UserReturn;
	Attr
		ere:EventReturn;
		ure:UserReturn;
End

Spec EventM;
	uses UtilOp,Integer,String,EventDB,UserDB,AbsData,EventReturn,EUReturn;
	Retr
		getEvent(Integer,EventDB):AbsData;
	Tran
		createEvent(Integer,Integer,String,EventDB):EventReturn;
		stopEvent(Integer,Integer,EventDB):EventReturn;
		updateEvent(Integer,Integer,Integer,EventDB):EventReturn;	//uid,eid,n
		stopAndPay(Integer,Integer,EventDB,UserDB):EUReturn;
	Axiom
		For all em:EventM, util:UtilOp, eid:Integer, db:EventDB that
			a.getEvent(eid,db) = null, if util.getDataById(eid,db) = nil;
			a.getEvent(eid,db) = util.getDataById(eid,db), if util.getDataById(eid,db) <> nil;
		End

		For all em:EventM, util:UtilOp, u,t:Integer, s:String, db:EventDB that
			let re = em.createEvent(u,t,s,db) in 
				util.isin(re.e, db.datas) = false;
				re.e.uid = u;
				re.e.des = s;
				re.e.target = t;
				re.e.total = 0;
				re.e.status = true;
				re.edb.datas = util.union(db.datas, re.e);
			End
		End

		For all em:EventM, util:UtilOp, u,i:Integer, db:EventDB that
			let 
				ev = util.getDataById(i,db) 
				re = em.stopEvent(u,i,db)
			in
				re.e.uid = ev.uid, if ev.uid = u, ev.status = true;
				re.e.des = ev.des, if ev.uid = u, ev.status = true;
				re.e.target = ev.target, if ev.uid = u, ev.status = true;
				re.e.total = ev.total, if ev.uid = u, ev.status = true;
				re.e.status = false, if ev.uid = u, ev.status = true;
				re.edb.datas = util.union(util.sub(db.datas, ev), re.e), if ev.uid = u, ev.status = true;

				re.e = null, if ev.uid <> u;
				re.edb = db, if ev.uid <> u;
				re.e = null, if ev.status = false;
				re.edb = db, if ev.status = false;
			End
		End

		For all em:EventM, util:UtilOp, u,i,n:Integer, db:EventDB that
			let 
				ev = util.getDataById(i,db) 
				re = em.updateEvent(u,i,n,db)
			in
				re.e.uid = ev.uid, if ev.status = true;
				re.e.des = ev.des, if ev.status = true;
				re.e.target = ev.target, if ev.status = true;
				re.e.total = ev.total + n, if ev.status = true;
				re.e.status = true, if ev.status = true;
				re.edb.datas = util.union(util.sub(db.datas, ev), re.e), if ev.status = true;

				re.e = null, if ev.status = false;
				re.edb = db, if ev.status = false;
			End
		End

		For all em:EventM, a:Account, u,i:Integer, db:EventDB, dbu:UserDB that
			let re = em.stopAndPay(u,i,edb,dbu) in
				re.ere = em.stopEvent(u,i,edb);
				re.ure = a.addBalance(u,re.ere.e.total,dbu), if re.ere.e <> null;
				re.ure.user = null, if re.ere.e = null;
				re.ure.udb = dbu, if re.ere.e = null;
			End
		End

		For all em:EventM, u1,u2,t:Int, s:string, db:EventDB that
			let 
				ere1 = em.createEvent(u1,t,s,db)
				ere2 = em.stopEvent(u2,ere1.id,ere1.edb)
			in
				ere2.e.status = false, if u1 = u2;
				ere2.e.total = 0, if u1 = u2;
				ere2.e.uid = u2, if u1 = u2;
				ere2.e = null, if u1 <> u2;
			End
		End

		For all em:EventM, u1,u2,t,n:Int, s:string, db:EventDB that
			let 
				ere1 = em.createEvent(u1,t,s,db)
				ere2 = em.updateEvent(u2,ere1.id,n,ere1.edb)
			in
				em.getEvent(ere1.id,ere2.edb).status = true;
				em.getEvent(ere1.id,ere2.edb).total = n;
				em.getEvent(ere1.id,ere2.edb).uid = u1;
			End
		End

		For all em:EventM, u,t,n:Int, s:string, db:EventDB, udb:UserDB that
			let 
				ere1 = em.createEvent(u,t,s,db)
				ere2 = em.updateEvent(u,ere1.id,n,ere1.edb)
				re = em.stopAndPay(u,ere1.id,ere2.edb,udb)
			in
				re.ere.e.status = false;
				re.ure.user.balance >= n, if re.ure.user != null;
				re.ere.e.total = n;
				re.ere.e.uid = u;
			End
		End
End
}
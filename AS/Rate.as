//14 axioms
package Rate;
import UtilOp;
{

Spec Limit;
	uses Integer;
	Attr
		dur:Integer;
	Axiom
		For all l:Limit that
			l.dur > 0;
		End
End

Spec RID;
	uses Integer, OpType;
	Attr
    	uid: Integer;
    	op: OpType;
End

Spec Recent;
	uses RID, Integer;
	Attr
		id: RID;
 		time: Integer;
 	Axiom
 		For all r:Recent that
 			r.time > 0;
 		End
End

Spec RDB;
	uses Recent;
	Attr
		datas[0..*]:RDB;
End

Spec RReturn;
	uses RID, Recent, RDB;
	Attr
		id: RID;
		rec: Recent;
		rdb: RDB;
End

Spec TReturn;
	uses Bool, RReturn;
	Attr
		status:Bool;
		rr:RReturn;
End

Spec Rate;
	uses RID,Recent,RDB,Integer,OpType,Limit,Bool,RReturn,TReturn;
	Retr
		checkRate(Integer,Integer,RID,OpType,Limit,RDB):Bool;	//uid, current time, ...
	Tran
		refreshTime(RID,Integer,db):RReturn;
		testFunc(Integer,Integer,RID,Limit,RDB):TReturn;
	Axiom
		For all ra:Rate, util:UtilOp, u,t:Integer, rid:RID, o:OpType, l:Limit, db:RDB that
			let r = util.getDataById(rid,db) in
				rid.uid = u;
				rid.op = o;
				ra.checkRate(u,t,rid,o,l,db) = false, if t - r.time < l.dur;
				ra.checkRate(u,t,rid,o,l,db) = true, if t - r.time >= l.dur;
				ra.checkRate(u,t,rid,o,l,db) = true, if r = nil;
			End
		End

		For all ra:Rate, util:UtilOp, rid:RID, t:Integer, db:RDB that
			let 
				r = util.getDataById(rid,db) 
				re = ra.refreshTime(rid,t,db)
			in
				re.rec.time = t;
				re.rdb.datas = util.union(util.sub(db.datas, r), re.rec);
			End
		End

		For all ra:Rate, u,t:Integer, rid:RID, l:Limit, db:RDB that
			ra.testFunc(u,t,rid,l,db).status = ra.checkRate(u,t,rid,TEST,l,db);
			ra.testFunc(u,t,rid,l,db).rr = ra.refreshTime(rid,t,db), if ra.testFunc(u,t,rid,l,db).status = true;
		End

		For all ra:Rate, u,t1,t2:Integer, rid:RID, l:Limit, db1,db2:RDB that
			let
				re1 = ra.testFunc(u,t1,rid,l,db1)
				re2 = ra.testFunc(u,t2,rid,l,db2)
			in
				re1.status = true, if db1.datas = nil;
				re2.status = false, if db1.datas = nil, db2 = re1.rr.rdb, t2-t1 < l.dur;
				re2.status = true, if db1.datas = nil, db2 = re1.rr.rdb, t2-t1 >= l.dur;
			End
		End
End
}
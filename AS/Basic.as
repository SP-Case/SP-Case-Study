package Basic;
{

Spec AbsData;
	uses Integer;
	Attr
		id:Integer;
End

Spec AbsDB;
	uses AbsData;
	Attr
		datas[0..*]:AbsData;
End

//--------------Alloy-------------------
//在SOFIA中，数据的唯一标识id作为数据的一个attribute，写在数据类子AbsData中
//在Alloy中，需要用一对一的关系（Int lone -> lone AbsData)表示数据id和数据的对应关系，写在数据库类子AbsDB中
//sig AbsData {}
//sig AbsDB {
//	datas: set Int lone -> lone AbsData 
//}

//------------null & nil----------------
//null表示内容为空的数据，需要在alloy中额外定义，继承自AbsData
//nil表示数据不存在，对应alloy中的 no

Spec OpType;
	Const:TEST, WD, RC, SE, DN;
End

}
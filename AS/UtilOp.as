package UtilOp;
import Basic;
{

//定义一系列公用操作，对应Alloy中的部分语法
Spec UtilOp;
	uses Integer, Bool, AbsData, AbsDB, Set;
	Retr
		//根据id获取数据对象，Alloy中的id.(db.datas)，表示通过数据库中id和数据的一对一关系获取对象
		getDataById(Integer, AbsDB):AbsData;
		//集合操作，判断元素是否在集合中, 对应Alloy中的in
		isin(AbsData, Set):Bool;
	Tran
		//集合操作，添加和删除元素, 对应Alloy中的 + 和 -
		union(Set, AbsData):Set;
		sub(Set, AbsData):Set;
End
}

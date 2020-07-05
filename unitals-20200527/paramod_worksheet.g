#! @Title Paramodifications of abstract unitals
#! @Subtitle GAP implementation and examples worksheet
#! @Author Gábor P. Nagy, Dávid Mezőfi

#! @Version 0.1
#! @Date 08/03/2020
#! @Address Bolyai Institute of the University of Szeged (Hungary) <Br />
#! @Address Department of Algebra of the Budapest University of Technology and Economics (Hungary)
#! @Abstract
#!  GAP implementation of paramodifications of abstract unitals. 
#!  With small modifications, it must work for other 2-designs as well.
#! @Copyright 2020 Gábor P. Nagy
#! @Acknowledgements Support provided from the National Research, 
#! Development and Innovation Fund of Hungary, financed under the 
#! 2018-1.2.1-NKP funding scheme, within the SETIT Project 
#! 2018-1.2.1-NKP-2018-00004. Partially supported by OTKA grants 
#! 119687 and 115288.

###############################################################################
#! @Chapter Commands for paramodifications
###############################################################################

###############################################################################
#! @Section Prerequisites
###############################################################################

#! The &GAP; packages <Package>UnitalSZ</Package> and <Package>GRAPE</Package> are necessary. 

#! @BeginExample
LoadPackage( "UnitalSZ", false );
LoadPackage( "grape", false );
#! @EndExample

#! You can use the info class <C>InfoParamod</C> to get extra information.

#! @BeginExample
DeclareInfoClass( "InfoParamod" ); 
#! @EndExample


#! @Arguments bls, k, gr
#! @Returns the list of block colorings of the set <A>bls</A> of blocks, with <A>k</A> 
#!  colors and color classes of size <C>|bls|/k</C>. The colorings are returned 
#!  as GAP transformation objects from <C>[1..Size(bls)]</C> to <C>[1..k]</C>.
#! @Description
#!  Let $P$ be a set, $B$ a set of subsets (called <E>blocks</E>), and $k$ a positive integer. 
#!  The map $\chi:B\to \{1,\ldots,k\}$ is a block coloring if $\chi(b)=\chi(b')$ implies
#!  $b\cap b'=\emptyset$ for any $b,b' \in B$. The block coloring in <E>regular</E>, if
#!  each color class has size $|B|/k$. The last argument <A>gr</A> must be a block
#!  preserving permutation of the set $P$ of points. 
DeclareGlobalFunction( "AllRegularBlockColorings" );

DeclareInfoClass( "InfoParamod" ); 

###############################################################################
#! @Section Paramodifications
###############################################################################

#! @Arguments u, b, chi
#! @Returns the paramodification of the unital <A>u</A> with respect to the 
#!  block <A>b</A> and regular block coloring <A>chi</A> with <C>|b|</C> colors.
#! @Description The coloring <A>chi</A> must be given as a GAP transformation 
#!  object from <C>[1..q^2*(q^2-q+1)]</C> to <C>[1..q+1]</C>, where <C>q</C> is 
#!  the order of <A>u</A>. This function has a slightly faster non-checking version 
#!  <C>ParamodificationOfUnitalNC</C>. 
DeclareGlobalFunction( "ParamodificationOfUnital" );

DeclareGlobalFunction( "ParamodificationOfUnitalNC" );

#! @Arguments u, b
#! @Returns all paramodifications of the unital <A>u</A> with respect to the block
#!   <A>b</A>. The results are reduced up to isomorphism of abstract unitals. 
DeclareGlobalFunction( "ParamodificationsOfUnitalWithBlock" );

#! @Arguments u
#! @Returns all paramodifications of the unital <A>u</A>. 
#!  The results are reduced up to isomorphism of abstract unitals. 
DeclareGlobalFunction( "AllParamodificationsOfUnital" );


###############################################################################
#! @Section Implementations
###############################################################################

#! @Subsection Regular block colorings
#! @BeginExample
InstallGlobalFunction( AllRegularBlockColorings, function( bls, nr_colors, gr )
	local Gamma, complete_subgraphs, graph_of_cliques, colorings, ret, new_blocks, c, c_vec, i, j;
	# construct the line graph and its cliques
	Gamma := Graph( gr, bls, OnSets,
        	function( x, y ) return x <> y and Intersection( x, y ) = [];
	end );
	complete_subgraphs := CompleteSubgraphs( Gamma, Size(bls)/nr_colors, 1);;
	complete_subgraphs := Union( List( complete_subgraphs,
				x -> Orbit( AutomorphismGroup( Gamma ), x, OnSets ) ) );
	Info( InfoParamod, 3, "cliques of the line graph computed..." );
	# construct the graph of cliques and its cliques
	graph_of_cliques := Graph( Gamma.group, complete_subgraphs, OnSets,
				function( x, y ) return x <> y and Intersection( x, y ) = [];
				end );
	colorings := CompleteSubgraphs( graph_of_cliques, nr_colors, 1 );
	Info( InfoParamod, 3, Size( colorings ), " block colorings computed..." );
	# construct colorings
	ret := [];
	for c in colorings do
		c_vec:=0*[1..Size(bls)];
		for i in [1..nr_colors] do 
			for j in VertexNames( graph_of_cliques )[c[i]] do
				c_vec[ Position( bls, VertexNames( Gamma )[j] ) ] := i;
			od;
		od;
		Add(ret, Transformation(c_vec));
	od;
	return ret;
end );
#! @EndExample

#! @Subsection Paramodifications
###############################################################################
# chi is a GAP transformation {1,...,|C(b)|} -> {1,...,|b|}
#! @BeginExample
InstallGlobalFunction( ParamodificationOfUnitalNC, function( u, b, chi )
	local Cb, n_Cb, C_star_b, intact_blks, B_star;
	Cb := Filtered( BlocksOfUnital( u ),
		x -> Size( Intersection( x, b ) ) = 1 );
	n_Cb := Length( Cb );
	C_star_b := List( [1..n_Cb],
		i -> Union( Difference( Cb[i], b ), [ b[i^chi] ] ) );
	intact_blks := Difference( BlocksOfUnital( u ), Cb );
	B_star := Union( intact_blks, C_star_b );
	return AbstractUnitalByDesignBlocks( B_star );
end );
#! @EndExample

###############################################################################
#! @BeginExample
InstallGlobalFunction( ParamodificationOfUnital, function( u, b, chi )
	local Cb;
	if not b in BlocksOfUnital( u ) then 
		Error( "argument 2 must be a block of argument 1");
	fi;
	Cb := Filtered( BlocksOfUnital( u ),
                   x -> Size( Intersection( x, b ) ) = 1 );
	Cb := List( Cb, x -> Difference( x, b) );
	if not ForAll( Combinations( [1..Size(Cb)], 2 ), p ->
			Intersection(Cb{p})=[] or 
			(p[1]^chi<>p[2]^chi)
		) then Error( "argument 3 is not a proper block coloring" ); 
	fi;
	return ParamodificationOfUnitalNC( u, b, chi );
end );
#! @EndExample

#! @Subsection Paramodifications with respect to a block
###############################################################################
#! @BeginExample
InstallGlobalFunction( ParamodificationsOfUnitalWithBlock, 
function( u, b )
	local q, Cb, b_stab, new_unitals, all, allchibmod, i, isom_class, colorings;
	if not b in BlocksOfUnital( u ) then 
		Error( "argument 2 must be a block of argument 1");
	fi;
	q := Order( u );
	Cb := Filtered( BlocksOfUnital( u ),
		x -> Size( Intersection( x, b ) ) = 1 );
	# Important: keep the order from BlocksOfUnital
	Cb := List( Cb, x -> Difference( x, b ) ); 
	# compute all colorings
	b_stab := Stabilizer( AutomorphismGroup( u ), b, OnSets );
	colorings := AllRegularBlockColorings( Cb, q + 1, b_stab );
	Info( InfoParamod, 1, Size( colorings ), " coloring(s) for the given unital-block pair computed..." );
	new_unitals := List( colorings, c -> ParamodificationOfUnitalNC( u, b, c ) );
	# reduction up to isomorphism
	all := [1..Length( new_unitals )];
	allchibmod := [];
	while all <> [] do
		i := Remove( all );
		isom_class := Filtered( all, x -> Isomorphism( new_unitals[i],
			new_unitals[x] ) <> fail ) ;
		all := Difference( all, isom_class );
		Add( allchibmod, new_unitals[i] );
	od;
	return allchibmod;
end );
#! @EndExample

#! @Subsection All paramodifications of a unital
###############################################################################
#! @BeginExample
InstallGlobalFunction( AllParamodificationsOfUnital, function( u )
	local blocks, rep_blocks, allchibmods, uus, b;
	blocks := BlocksOfUnital( u );
	rep_blocks := List( Orbits( AutomorphismGroup( u ), blocks, OnSets ),
		      orb -> Representative( orb ) );
	Info( InfoParamod, 2, Size( rep_blocks ), " block representatives for the unital computed..." );
	allchibmods := [];
	for b in rep_blocks do
		uus := ParamodificationsOfUnitalWithBlock( u, b );
		uus := Filtered( uus, x -> Isomorphism( x, u ) = fail and
				ForAll( allchibmods, y -> Isomorphism( y, x ) = fail ) );
		Append( allchibmods, uus );
	od;
	return allchibmods;
end );
#! @EndExample
###############################################################################

###############################################################################
#! @Chapter Examples
###############################################################################

###############################################################################
#! @Section Computing paramodifications
###############################################################################

#! @BeginExample
LoadPackage( "UnitalSZ", false );
LoadPackage( "grape", false );
u:=KNPAbstractUnital(1577);
#! KNPAbstractUnital(1577)
AutomorphismGroup(u);
#! <permutation group with 6 generators>
b:=BlocksOfUnital(u)[1];
#! [ 1, 2, 5, 6, 14 ]
bls0:=Filtered(BlocksOfUnital(u),x->Size(Intersection(x,b))=1);;
bls:=List(bls0,x->Difference(x,b));;

cols:=AllRegularBlockColorings(bls,5,Group(())); time;
#! [ Transformation( [ 1, 1, 1, 4, 2, 5, 3, 5, 3, 4, 2, 2, 5, 3, 4, 4, 3, 2, 5, 5, 3, 4, 4, 5, 3, 2, 2, 1, 1, 1, 5, 3, 2, 4, 5, 2, 5,
#!      4, 3, 2, 2, 3, 2, 5, 3, 4, 1, 1, 1, 4, 2, 4, 4, 5, 2, 3, 2, 5, 3, 1, 1, 1, 3, 3, 2, 5, 3, 5, 4, 4, 4, 5, 1, 1, 1 ] ), 
#!   Transformation( [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 2, 4, 2, 3, 3, 2, 4, 2, 5, 5, 5, 5, 3, 2, 2, 4, 5, 2,
#!      5, 3, 5, 3, 2, 2, 3, 5, 3, 4, 4, 4, 4, 3, 5, 3, 5, 4, 4, 5, 3, 5, 2, 2, 2, 5, 2, 4, 2, 4, 5, 5, 4, 2, 4, 3, 3, 3 ] ), 
#!   Transformation( [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 5, 5, 5, 3, 3, 3, 5, 3, 3, 5, 4, 5, 3, 2, 2, 5, 3, 2,
#!      5, 2, 4, 2, 5, 5, 4, 4, 4, 4, 2, 5, 5, 3, 3, 2, 3, 2, 2, 5, 2, 5, 5, 3, 2, 3, 2, 4, 3, 4, 4, 4, 2, 3, 2, 4, 2, 3 ] ), 
#!   Transformation( [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 3, 2, 5, 3, 2, 5,
#!      5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ] ), 
#!   Transformation( [ 1, 2, 5, 5, 5, 5, 5, 2, 1, 2, 2, 1, 1, 2, 1, 4, 4, 4, 4, 2, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 3, 2, 1, 3, 5, 1,
#!      5, 1, 4, 1, 5, 5, 4, 4, 4, 4, 1, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 2, 4, 5, 4, 4, 4, 2, 5, 2, 4, 2, 5 ] ), 
#!   Transformation( [ 1, 3, 4, 4, 4, 4, 4, 3, 1, 3, 3, 1, 1, 3, 1, 4, 4, 4, 4, 5, 5, 5, 1, 1, 1, 5, 1, 1, 5, 4, 5, 3, 2, 1, 5, 2, 1,
#!      5, 1, 3, 1, 5, 5, 3, 3, 3, 3, 1, 5, 5, 3, 3, 4, 3, 4, 4, 5, 4, 5, 5, 3, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ] ), 
#!   Transformation( [ 1, 2, 4, 4, 4, 4, 4, 2, 1, 2, 2, 1, 1, 2, 1, 4, 4, 4, 4, 2, 2, 2, 3, 3, 3, 2, 3, 3, 2, 4, 5, 3, 2, 5, 1, 3, 5,
#!      5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 1, 3, 3, 4, 3, 4, 4, 1, 4, 1, 1, 3, 4, 3, 2, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 3 ] ), 
#!   Transformation( [ 1, 3, 5, 5, 5, 5, 5, 3, 1, 3, 3, 1, 1, 3, 1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 3, 2, 2, 1, 5, 2,
#!      5, 2, 3, 2, 5, 5, 3, 3, 3, 3, 2, 5, 1, 3, 3, 2, 3, 2, 2, 1, 2, 1, 1, 3, 2, 5, 2, 1, 5, 1, 1, 1, 2, 5, 2, 1, 2, 5 ] ), 
#!   Transformation( [ 1, 5, 2, 1, 5, 1, 5, 2, 2, 2, 1, 2, 5, 1, 5, 4, 1, 1, 4, 1, 4, 1, 3, 3, 3, 4, 3, 3, 5, 2, 5, 3, 2, 2, 4, 3, 2,
#!      5, 5, 2, 5, 1, 1, 1, 2, 1, 4, 4, 4, 4, 3, 3, 5, 3, 4, 4, 5, 5, 5, 1, 3, 2, 3, 2, 4, 3, 4, 2, 2, 4, 3, 4, 1, 5, 3 ] ), 
#!   Transformation( [ 1, 4, 3, 1, 4, 1, 4, 3, 3, 3, 1, 3, 4, 1, 4, 4, 1, 1, 4, 1, 3, 1, 3, 3, 4, 3, 4, 5, 5, 5, 5, 3, 2, 2, 3, 5, 2,
#!      5, 2, 5, 2, 1, 1, 1, 5, 1, 4, 2, 3, 3, 3, 5, 2, 5, 2, 2, 5, 2, 5, 1, 4, 2, 5, 2, 4, 4, 4, 5, 5, 2, 4, 2, 1, 2, 3 ] ), 
#!   Transformation( [ 1, 4, 2, 1, 4, 1, 4, 2, 2, 2, 1, 2, 4, 1, 4, 4, 3, 3, 4, 5, 5, 5, 3, 3, 4, 5, 4, 1, 5, 2, 5, 3, 2, 2, 5, 1, 2,
#!      5, 3, 2, 3, 5, 5, 3, 2, 3, 4, 1, 5, 5, 3, 1, 3, 1, 1, 1, 5, 3, 5, 5, 4, 2, 1, 2, 4, 4, 4, 2, 2, 1, 4, 1, 3, 3, 3 ] ), 
#!   Transformation( [ 1, 5, 3, 1, 5, 1, 5, 3, 3, 3, 1, 3, 5, 1, 5, 4, 4, 4, 4, 2, 3, 2, 3, 3, 2, 3, 2, 1, 5, 4, 5, 3, 2, 2, 3, 1, 2,
#!      5, 5, 4, 5, 2, 2, 4, 4, 4, 4, 1, 3, 3, 3, 1, 5, 1, 1, 1, 5, 5, 5, 2, 2, 2, 1, 2, 4, 2, 4, 4, 4, 1, 2, 1, 4, 5, 3 ] ) ]
#! 342
List(cols,c->ParamodificationOfUnitalNC(u,b,c)); time;
#! [ AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, 
#!   AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4> ]
#! 32
List(cols,c->ParamodificationOfUnital(u,b,c)); time;
#! [ AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, 
#!   AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4> ]
#! 88

ParamodificationsOfUnitalWithBlock(u,b); time;
#! [ AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4> ]
#! 219
AllParamodificationsOfUnital(u); time;
#! [ AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, 
#!   AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4>, AU_UnitalDesign<4> ]
#! 961
#! @EndExample

###############################################################################
#! @Section Para-rigidity of cyclic unitals
###############################################################################

#! We say that a unital is **para-rigid**, if all block colorings of $C(b)$ are equivalent with the trivial one.
#! The following example shows that the cyclic unitals of order 4 and 6 by Bagchi and Bagchi are para-rigid.

#! @BeginExample
SetInfoLevel(InfoParamod,2);
u:=BagchiBagchiCyclicUnital(4);
#! BagchiBagchiCyclicUnital(4)
AllParamodificationsOfUnital(u);
#! #I  2 block representatives for the unital computed...
#! #I  1 coloring(s) for the given unital-block pair computed...
#! #I  1 coloring(s) for the given unital-block pair computed...
#! [  ]
u:=BagchiBagchiCyclicUnital(6);
#! BagchiBagchiCyclicUnital(6)
AllParamodificationsOfUnital(u);
#! #I  2 block representatives for the unital computed...
#! #I  1 coloring(s) for the given unital-block pair computed...
#! #I  1 coloring(s) for the given unital-block pair computed...
#! [  ]
#! @EndExample


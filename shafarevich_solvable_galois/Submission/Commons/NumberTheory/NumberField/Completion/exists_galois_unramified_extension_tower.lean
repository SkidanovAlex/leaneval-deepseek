import Lean.Parser.Command
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Cardinal
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Subfield
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Ring.Shrink
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.Algebra.Torsor.Defs
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.Analysis.Asymptotics.TVS
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Finite.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Rel
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Computability.Language
import Mathlib.Computability.Reduce
import Mathlib.Control.Fix
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Shrink
import Mathlib.Data.FunLike.Fintype
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Star
import Mathlib.Data.List.Lex
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Rat.Star
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Fintype
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Dynamics.Flow
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.ConjRootClass
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.GroupTheory.CosetCover
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.OfQuotient
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Lattice
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.SetTheory.ZFC.Class
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Cases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.PowMod
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Torsor
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.NumberTheory.NumberField.exists_frobenius_galRestrict
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped IntermediateField NumberField
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.NumberField.Completion

/-- Arithmetic: `q^n - 1` divides `q^k - 1` exactly when `n` divides `k`. -/
lemma dvd_pow_sub_one_iff {q n k : ℕ} (hq : 2 ≤ q) (hn : 0 < n) :
    q ^ n - 1 ∣ q ^ k - 1 ↔ n ∣ k := by
  have h1q : 1 ≤ q := by omega
  refine ⟨fun h => ?_, fun h => Nat.pow_sub_one_dvd_pow_sub_one q h⟩
  set r := k % n with hr
  have hrlt : r < n := Nat.mod_lt k hn
  have hk : n * (k / n) + r = k := by rw [hr]; exact Nat.div_add_mod k n
  set N := n * (k / n) with hN
  have hNk : N + r = k := hk
  have hpow : q ^ k = q ^ N * q ^ r := by rw [← hNk, pow_add]
  have hdN : q ^ n - 1 ∣ q ^ N - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one q (by rw [hN]; exact dvd_mul_right n (k / n))
  have hNle : N ≤ k := by rw [hN]; exact Nat.mul_div_le k n
  have hdNr : q ^ n - 1 ∣ q ^ N * (q ^ r - 1) := by
    have hEq : q ^ N * (q ^ r - 1) = (q ^ k - 1) - (q ^ N - 1) := by
      have hle : q ^ N ≤ q ^ k := Nat.pow_le_pow_right (by omega) hNle
      have hle1 : 1 ≤ q ^ N := Nat.one_le_pow N q (by omega)
      have hle2 : 1 ≤ q ^ k := Nat.one_le_pow k q (by omega)
      have hA : q ^ N * (q ^ r - 1) = q ^ k - q ^ N := by
        rw [Nat.mul_sub_left_distrib, mul_one, ← hpow]
      have hB : (q ^ k - 1) - (q ^ N - 1) = q ^ k - q ^ N := by omega
      rw [hA, hB]
    rw [hEq]
    exact Nat.dvd_sub h hdN
  have h3 : q ^ n - 1 ∣ q ^ r - 1 := by
    have hkey : q ^ N * (q ^ r - 1) - (q ^ N - 1) * (q ^ r - 1) = q ^ r - 1 := by
      rw [Nat.sub_mul, one_mul]
      exact Nat.sub_sub_self (Nat.le_mul_of_pos_left (q ^ r - 1) (pow_pos (by omega) N))
    rw [← hkey]
    exact Nat.dvd_sub hdNr (Dvd.dvd.mul_right hdN _)
  have hlt : q ^ r - 1 < q ^ n - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_pow r q (by omega))
      (Nat.pow_lt_pow_right (by omega) hrlt)
  have hzero : q ^ r - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h3 hlt
  have hr0 : r = 0 := by
    have hqr : q ^ r = 1 :=
      le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) (Nat.one_le_pow r q (by omega))
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exact h0
    · exfalso
      have h2 : 2 ≤ q ^ r := by
        calc 2 ≤ q := hq
          _ = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ r := Nat.pow_le_pow_right (by omega) h0
      rw [hqr] at h2
      exact absurd h2 (by norm_num)
  rw [← hNk, hr0, add_zero]
  exact dvd_mul_right n (k / n)

/-- In a number field, a root of unity of order dividing `N` which is congruent to `1` modulo a
prime `P` with `N ∉ P` is `1`. -/
lemma eq_one_of_pow_eq_one_of_sub_mem {K : Type} [Field K] [NumberField K] {P : Ideal (𝓞 K)}
    {N : ℕ} {η : 𝓞 K} (hη : η ^ N = 1) (hsub : η - 1 ∈ P)
    (hN : ((N : ℕ) : 𝓞 K) ∉ P) : η = 1 := by
  by_contra hne
  obtain ⟨c, hc⟩ := sub_one_dvd_natCast_of_pow_eq_one hη hne
  exact hN (hc ▸ Ideal.mul_mem_right c P hsub)

/-- In a number field, two roots of unity of order dividing `N` which are congruent modulo a prime
`P` with `N ∉ P` are equal. -/
lemma eq_of_sub_mem_of_pow_eq_one {K : Type} [Field K] [NumberField K] {P : Ideal (𝓞 K)}
    {N : ℕ} {θ η : 𝓞 K} (hθ : θ ^ N = 1) (hη : η ^ N = 1) (hsub : θ - η ∈ P)
    (hN : ((N : ℕ) : 𝓞 K) ∉ P) : θ = η := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · exfalso
    refine hN ?_
    rw [hN0, Nat.cast_zero]
    exact P.zero_mem
  have hN1 : 1 ≤ N := hNpos
  have hζ : θ * η ^ N = θ := by rw [hη, mul_one]
  have hζ1 : (θ * η ^ (N - 1)) ^ N = 1 := by
    rw [mul_pow, hθ, one_mul, ← pow_mul, mul_comm, pow_mul, hη, one_pow]
  have hsub' : θ * η ^ (N - 1) - 1 ∈ P := by
    have hEq : θ * η ^ (N - 1) - 1 = (θ - η) * η ^ (N - 1) := by
      have h2 : (θ - η) * η ^ (N - 1) = θ * η ^ (N - 1) - η ^ N := by
        rw [sub_mul, ← pow_succ', Nat.sub_add_cancel hN1]
      rw [h2, hη]
    rw [hEq]
    exact Ideal.mul_mem_right _ _ hsub
  have hone : θ * η ^ (N - 1) = 1 := eq_one_of_pow_eq_one_of_sub_mem hζ1 hsub' hN
  calc θ = θ * η ^ N := hζ.symm
    _ = θ * η ^ (N - 1) * η := by rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hN1]
    _ = η := by rw [hone, one_mul]

/-- The cardinality of the residue field of a finite place lies in the place. -/
lemma natCard_residueField_mem {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    ((Nat.card (𝓞 L ⧸ q.asIdeal) : ℕ) : 𝓞 L) ∈ q.asIdeal := by
  haveI hfin : Finite (𝓞 L ⧸ q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
  haveI hft : Fintype (𝓞 L ⧸ q.asIdeal) := Fintype.ofFinite (𝓞 L ⧸ q.asIdeal)
  letI : Field (𝓞 L ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_natCast]
  have h := FiniteField.cast_card_eq_zero (𝓞 L ⧸ q.asIdeal)
  rw [Nat.card_eq_fintype_card]
  exact h

theorem exists_galois_unramified_extension_tower
    {L : Type} [Field L] [NumberField L] {L' : Type} [Field L'] [NumberField L']
    [Algebra L L'] [FiniteDimensional L L'] [IsGalois L L']
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'))
    (hq : q'.asIdeal.LiesOver q.asIdeal) (n : ℕ) (hn : 0 < n) :
    ∃ (L'' : Type) (_ : Field L'') (_ : NumberField L'') (_ : Algebra L L'')
      (_ : Algebra L' L'') (_ : IsScalarTower L L' L'') (_ : FiniteDimensional L L'')
      (_ : IsGalois L L'') (_ : IsGalois L' L'')
      (q'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'')),
      q''.asIdeal.LiesOver q'.asIdeal ∧
      q''.asIdeal.ramificationIdx (NumberField.RingOfIntegers L') = 1 ∧
      q''.asIdeal.inertiaDeg (NumberField.RingOfIntegers L') = n := by
  classical
  -- ============ Step 0: the numerical data ============
  haveI hfin : Finite (NumberField.RingOfIntegers L' ⧸ q'.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q'
  haveI hfint : Fintype (NumberField.RingOfIntegers L' ⧸ q'.asIdeal) := Fintype.ofFinite _
  set qN : ℕ := Nat.card (NumberField.RingOfIntegers L' ⧸ q'.asIdeal) with hqN
  have hqN2 : 2 ≤ qN := by
    rw [hqN, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  set m : ℕ := qN ^ n - 1 with hm
  have hmpos : 0 < m := by
    have h1 : 1 < qN ^ n := one_lt_pow₀ (by omega) hn.ne'
    omega
  haveI hmne : NeZero m := ⟨hmpos.ne'⟩
  -- ============ Step 1: the ambient field and the subfields ============
  let Ω := AlgebraicClosure L
  let ι : L' →ₐ[L] Ω := IsAlgClosed.lift
  have hι : Function.Injective ι := ι.toRingHom.injective
  let E1 : IntermediateField L Ω := ι.fieldRange
  let e1 : L' ≃ₐ[L] ↥E1 := AlgEquiv.ofInjective ι hι
  haveI hE1fin : FiniteDimensional L ↥E1 := LinearEquiv.finiteDimensional e1.toLinearEquiv
  haveI hE1gal : IsGalois L ↥E1 := IsGalois.of_algEquiv e1
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ m := by
    obtain ⟨ζ, hζr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic m Ω) (by
      rw [Polynomial.degree_cyclotomic]
      simpa using (Nat.totient_pos.mpr hmpos).ne')
    exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζr⟩
  let E2 : IntermediateField L Ω := IntermediateField.adjoin L {ζ}
  haveI hE2cyc : IsCyclotomicExtension {m} L ↥E2 :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension L hζ
  haveI hE2fin : FiniteDimensional L ↥E2 := by
    refine IntermediateField.adjoin.finiteDimensional ?_
    exact ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hmpos.ne',
      by simpa [sub_eq_zero] using hζ.pow_eq_one⟩
  haveI hE2gal : IsGalois L ↥E2 := IsCyclotomicExtension.isGalois {m} L ↥E2
  let L'' : IntermediateField L Ω := E1 ⊔ E2
  haveI hgalL : IsGalois L ↥L'' := ⟨⟩
  haveI hfinL : FiniteDimensional L ↥L'' := IntermediateField.finiteDimensional_sup E1 E2
  haveI hnf : NumberField ↥L'' :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := L) (K' := Ω) L''
  -- ============ Step 2: the algebra structure over L' ============
  have hE1le : E1 ≤ L'' := le_sup_left
  let φ : L' →ₐ[L] ↥L'' := (IntermediateField.inclusion hE1le).comp e1.toAlgHom
  letI : Algebra L' ↥L'' := φ.toRingHom.toAlgebra
  haveI hST : IsScalarTower L L' ↥L'' := IsScalarTower.of_algebraMap_eq (fun x => by
    change (algebraMap L ↥L'') x = φ (algebraMap L L' x)
    rw [show φ (algebraMap L L' x) =
        (IntermediateField.inclusion hE1le) (e1 (algebraMap L L' x)) from rfl, e1.commutes x]
    exact ((IntermediateField.inclusion hE1le).commutes x).symm)
  haveI hgalL' : IsGalois L' ↥L'' := IsGalois.tower_top_of_isGalois L L' ↥L''
  haveI hfinL' : FiniteDimensional L' ↥L'' := FiniteDimensional.right L L' ↥L''
  -- ============ Step 3: the prime q'' over q' ============
  obtain ⟨q'', hq''⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := L') (L := ↥L'') q'
  -- ============ Step 4: the primitive root of unity as an integral element ============
  have hxζmem : ζ ∈ (L'' : Set Ω) :=
    (SetLike.coe_subset_coe.mpr le_sup_right)
      (IntermediateField.subset_adjoin L ({ζ} : Set Ω) (Set.mem_singleton ζ))
  let xζ : ↥L'' := ⟨ζ, hxζmem⟩
  have hxζcoe : (xζ : Ω) = ζ := rfl
  have hxζprim : IsPrimitiveRoot xζ m := by
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      show (xζ : Ω) ^ m = 1
      rw [hxζcoe]
      exact hζ.pow_eq_one
    · intro l hl
      apply hζ.dvd_of_pow_eq_one l
      have h : ((xζ ^ l : ↥L'') : Ω) = ((1 : ↥L'') : Ω) := congrArg Subtype.val hl
      simpa [hxζcoe] using h
  have hxζm : xζ ^ m = 1 := hxζprim.pow_eq_one
  have hxζint : IsIntegral ℤ xζ :=
    ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hmpos.ne',
      by
        show Polynomial.eval₂ (algebraMap ℤ ↥L'') xζ (Polynomial.X ^ m - Polynomial.C 1) = 0
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
          hxζm, map_one, sub_self]⟩
  obtain ⟨Θ, hΘ⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 ↥L'') (R := ℤ)
    (B := ↥L'')).mp hxζint
  have hΘm : Θ ^ m = 1 := by
    have h2 : (algebraMap (𝓞 ↥L'') ↥L'') (Θ ^ m) = (algebraMap (𝓞 ↥L'') ↥L'') 1 := by
      rw [map_pow, map_one, hΘ, hxζm]
    exact IsIntegralClosure.algebraMap_injective (𝓞 ↥L'') ℤ ↥L'' h2
  have hxζne : xζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hmpos.ne'] at hxζm
    exact one_ne_zero hxζm.symm
  -- ============ Step 5: the faithfulness of the action on `ζ` ============
  have hfaith : ∀ σ : ↥L'' ≃ₐ[L'] ↥L'', σ xζ = xζ → σ = 1 := by
    intro σ hσζ
    have hE2le : (E2 : Set Ω) ⊆ (L'' : Set Ω) := SetLike.coe_subset_coe.mpr le_sup_right
    have hE2fix : ∀ (x : Ω) (hx : x ∈ E2), ∀ hx' : x ∈ (L'' : Set Ω),
        σ ⟨x, hx'⟩ = ⟨x, hx'⟩ := by
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem y hy =>
          intro hy'
          have h1 : (⟨y, hy'⟩ : ↥L'') = xζ := by
            apply Subtype.ext
            exact Set.mem_singleton_iff.mp hy
          rw [h1, hσζ]
      | algebraMap y =>
          intro hy'
          have h1 : (⟨algebraMap L Ω y, hy'⟩ : ↥L'') = algebraMap L ↥L'' y := by
            apply Subtype.ext
            rfl
          rw [h1, IsScalarTower.algebraMap_apply L L' ↥L'', AlgEquiv.commutes]
      | add y z hy hz ihy ihz =>
          intro hy'
          rw [show (⟨y + z, hy'⟩ : ↥L'') = ⟨y, hE2le hy⟩ + ⟨z, hE2le hz⟩ from rfl,
            map_add, ihy (hE2le hy), ihz (hE2le hz)]
      | inv y hy ihy =>
          intro hy'
          rw [show (⟨y⁻¹, hy'⟩ : ↥L'') = (⟨y, hE2le hy⟩ : ↥L'')⁻¹ from rfl, map_inv₀,
            ihy (hE2le hy)]
      | mul y z hy hz ihy ihz =>
          intro hy'
          rw [show (⟨y * z, hy'⟩ : ↥L'') = ⟨y, hE2le hy⟩ * ⟨z, hE2le hz⟩ from rfl,
            map_mul, ihy (hE2le hy), ihz (hE2le hz)]
    have hmain : ∀ (x : Ω) (hx : x ∈ (E1 ⊔ E2 : IntermediateField L Ω)),
        ∀ hx' : x ∈ (L'' : Set Ω), σ ⟨x, hx'⟩ = ⟨x, hx'⟩ := by
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem y hy =>
          intro hy'
          rcases hy with hy | hy
          · obtain ⟨z, rfl⟩ := (AlgHom.mem_fieldRange).mp hy
            have h1 : (⟨ι z, hy'⟩ : ↥L'') = algebraMap L' ↥L'' z := by
              apply Subtype.ext
              rfl
            rw [h1, AlgEquiv.commutes]
          · exact hE2fix y hy hy'
      | algebraMap y =>
          intro hy'
          have h1 : (⟨algebraMap L Ω y, hy'⟩ : ↥L'') = algebraMap L ↥L'' y := by
            apply Subtype.ext
            rfl
          rw [h1, IsScalarTower.algebraMap_apply L L' ↥L'', AlgEquiv.commutes]
      | add y z hy hz ihy ihz =>
          intro hy'
          rw [show (⟨y + z, hy'⟩ : ↥L'') = ⟨y, hy⟩ + ⟨z, hz⟩ from rfl,
            map_add, ihy hy, ihz hz]
      | inv y hy ihy =>
          intro hy'
          rw [show (⟨y⁻¹, hy'⟩ : ↥L'') = (⟨y, hy⟩ : ↥L'')⁻¹ from rfl, map_inv₀, ihy hy]
      | mul y z hy hz ihy ihz =>
          intro hy'
          rw [show (⟨y * z, hy'⟩ : ↥L'') = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl,
            map_mul, ihy hy, ihz hz]
    ext x
    simpa using hmain (x : Ω) x.2 x.2
  -- ============ Step 6: `m` is a unit at `q''` ============
  have hqle : q'.asIdeal ≤ Ideal.comap (algebraMap (𝓞 L') (𝓞 ↥L'')) q''.asIdeal :=
    le_of_eq (Ideal.LiesOver.over (P := q''.asIdeal) (p := q'.asIdeal))
  let ψ : (𝓞 L' ⧸ q'.asIdeal) →+* (𝓞 ↥L'' ⧸ q''.asIdeal) :=
    Ideal.Quotient.lift q'.asIdeal
      ((Ideal.Quotient.mk q''.asIdeal).comp (algebraMap (𝓞 L') (𝓞 ↥L'')))
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hqle ha)
  haveI : Field (𝓞 L' ⧸ q'.asIdeal) := Ideal.Quotient.field q'.asIdeal
  haveI : Field (𝓞 ↥L'' ⧸ q''.asIdeal) := Ideal.Quotient.field q''.asIdeal
  have hqNmem : ((qN : ℕ) : 𝓞 L') ∈ q'.asIdeal := by
    rw [hqN]
    exact natCard_residueField_mem q'
  have hqNzero : (Ideal.Quotient.mk q'.asIdeal ((qN : ℕ) : 𝓞 L')) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hqNmem
  have hqNzero'' : (Ideal.Quotient.mk q''.asIdeal ((qN : ℕ) : 𝓞 ↥L'')) = 0 := by
    have h := congrArg ψ hqNzero
    rw [map_zero] at h
    rw [show ψ (Ideal.Quotient.mk q'.asIdeal ((qN : ℕ) : 𝓞 L')) =
        Ideal.Quotient.mk q''.asIdeal
          (algebraMap (𝓞 L') (𝓞 ↥L'') ((qN : ℕ) : 𝓞 L')) from
      Ideal.Quotient.lift_mk q'.asIdeal _ _] at h
    rwa [map_natCast] at h
  have hmm : (Ideal.Quotient.mk q''.asIdeal ((m : ℕ) : 𝓞 ↥L'')) ≠ 0 := by
    have hm1 : m + 1 = qN ^ n := by omega
    have h1 : (Ideal.Quotient.mk q''.asIdeal ((m : ℕ) : 𝓞 ↥L'')) + 1 = 0 := by
      have hsum : ((m : ℕ) : 𝓞 ↥L'') + 1 = ((qN ^ n : ℕ) : 𝓞 ↥L'') := by
        rw [← Nat.cast_one, ← Nat.cast_add, hm1]
      have hpow : ((qN ^ n : ℕ) : 𝓞 ↥L'') = ((qN : ℕ) : 𝓞 ↥L'') ^ n := Nat.cast_pow qN n
      have h3 : Ideal.Quotient.mk q''.asIdeal (((m : ℕ) : 𝓞 ↥L'') + 1) = 0 := by
        rw [hsum, hpow, map_pow, hqNzero'', zero_pow hn.ne']
      rwa [map_add, map_one] at h3
    intro h0
    rw [h0, zero_add] at h1
    exact one_ne_zero h1
  have hm_unit : ((m : ℕ) : 𝓞 ↥L'') ∉ q''.asIdeal := by
    intro hmem
    exact hmm (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  -- ============ Step 7: `e(q''|q') = 1` ============
  have he : q''.asIdeal.ramificationIdx (𝓞 L') = 1 := by
    haveI : q''.asIdeal.LiesOver q'.asIdeal := hq''
    rw [← Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      q'.asIdeal q''.asIdeal]
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    refine hfaith σ ?_
    have hmem : σ • Θ - Θ ∈ q''.asIdeal :=
      (AddSubgroup.mem_inertia.mp (show σ ∈ (q''.asIdeal.toAddSubgroup).inertia
        (↥L'' ≃ₐ[L'] ↥L'') from hσ)) Θ
    have hθm : (σ • Θ) ^ m = 1 := by
      have h := map_pow (MulSemiringAction.toRingHom (↥L'' ≃ₐ[L'] ↥L'') (𝓞 ↥L'') σ) Θ m
      rw [hΘm, map_one] at h
      exact h.symm
    have hσΘ : σ • Θ = Θ := eq_of_sub_mem_of_pow_eq_one hθm hΘm hmem hm_unit
    have hcoe : ((σ • Θ : 𝓞 ↥L'') : ↥L'') = σ xζ := by
      rw [Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.smul_ringOfIntegers_eq_galRestrict]
      change (algebraMap (𝓞 ↥L'') ↥L'') (galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ) = σ xζ
      rw [algebraMap_galRestrict_apply (𝓞 L') σ Θ]
      exact congrArg σ hΘ
    rw [← hcoe, hσΘ]
    change (algebraMap (𝓞 ↥L'') ↥L'') Θ = xζ
    exact hΘ
  -- ============ Step 8: `f(q''|q') = n` ============
  have hf : q''.asIdeal.inertiaDeg (𝓞 L') = n := by
    obtain ⟨σ, hσmap, hσres⟩ :=
      Commons.NumberTheory.NumberField.exists_frobenius_galRestrict (K := L') (L := ↥L'') q' q'' hq''
    have hresΘ : (Ideal.Quotient.mk q''.asIdeal
          (galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ)) =
        (Ideal.Quotient.mk q''.asIdeal Θ) ^ qN := by
      have h := hσres Θ
      rwa [← hqN] at h
    have hsub : galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ - Θ ^ qN ∈ q''.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hresΘ, map_pow, sub_self]
    have hθm : (galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ) ^ m = 1 := by
      have h : (σ • Θ) ^ m = 1 := by
        have h2 := map_pow (MulSemiringAction.toRingHom (↥L'' ≃ₐ[L'] ↥L'') (𝓞 ↥L'') σ) Θ m
        rw [hΘm, map_one] at h2
        exact h2.symm
      rwa [← Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.smul_ringOfIntegers_eq_galRestrict]
    have hΘqm : (Θ ^ qN) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hΘm, one_pow]
    have hσΘ : galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ = Θ ^ qN :=
      eq_of_sub_mem_of_pow_eq_one hθm hΘqm hsub hm_unit
    have hσxζ : σ xζ = xζ ^ qN := by
      have hcoe : ((galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ : 𝓞 ↥L'') : ↥L'') = σ xζ := by
        change (algebraMap (𝓞 ↥L'') ↥L'') (galRestrict (𝓞 L') L' ↥L'' (𝓞 ↥L'') σ Θ) = σ xζ
        rw [algebraMap_galRestrict_apply (𝓞 L') σ Θ]
        exact congrArg σ hΘ
      rw [← hcoe, hσΘ]
      rw [show ((Θ ^ qN : 𝓞 ↥L'') : ↥L'') = (algebraMap (𝓞 ↥L'') ↥L'') (Θ ^ qN) from rfl,
        map_pow]
      exact congrArg (fun z => z ^ qN) hΘ
    have hpow : ∀ k : ℕ, (σ ^ k) xζ = xζ ^ (qN ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', AlgEquiv.mul_apply, ih]
          rw [show σ (xζ ^ qN ^ k) = (σ xζ) ^ (qN ^ k) from map_pow (σ : ↥L'' →+* ↥L'') _ _]
          rw [hσxζ, ← pow_mul, ← pow_succ']
    have hord : orderOf σ = n := by
      rw [orderOf_eq_iff hn]
      refine ⟨?_, ?_⟩
      · apply hfaith (σ ^ n)
        rw [hpow n]
        rw [show qN ^ n = m + 1 by omega, pow_succ, hxζm, one_mul]
      · intro k hk hkpos hk1
        have h1 : (σ ^ k) xζ = xζ := by rw [hk1]; rfl
        rw [hpow k] at h1
        have h2 : xζ ^ (qN ^ k - 1) = 1 := by
          have hqk1 : 1 ≤ qN ^ k := Nat.one_le_pow k qN (by omega)
          have h3 : xζ ^ (qN ^ k - 1) * xζ = xζ := by
            rw [← pow_succ, Nat.sub_add_cancel hqk1]
            exact h1
          exact mul_right_cancel₀ hxζne (by rw [h3, one_mul])
        have h4 : m ∣ qN ^ k - 1 := (hxζprim.pow_eq_one_iff_dvd _).mp h2
        have h5 : n ∣ k := (dvd_pow_sub_one_iff hqN2 hn).mp h4
        obtain ⟨c, hc⟩ := h5
        rw [hc] at hk
        have hk' : n * c < n * 1 := by
          rw [mul_one]
          exact hk
        have hc1 : c < 1 := (Nat.mul_lt_mul_left hn).mp hk'
        have hcpos : 0 < c := by
          rcases Nat.eq_zero_or_pos c with h0 | h0
          · rw [hc, h0, mul_zero] at hkpos
            exact absurd hkpos (lt_irrefl 0)
          · exact h0
        omega
    rw [← Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
      q' q'' hq'' he σ hσmap hσres]
    exact hord
  exact ⟨↥L'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, q'', hq'', he, hf⟩

end Commons.NumberTheory.NumberField.Completion

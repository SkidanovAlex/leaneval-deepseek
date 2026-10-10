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
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_isNormal_card_quotient
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_val_lt_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum Polynomial

/-! ## The integer ring map and the natural map of residue fields

For the extension `L / K` of number fields and the places `q | Q` we construct, from
`adicCompletionMap Q q hq`, the ring homomorphism of integer rings
`intCompletionMap Q q hq : Q.adicCompletionIntegers K →+* q.adicCompletionIntegers L`, and the
induced map `natResidueMap Q q hq` of residue fields.  The latter is the natural map
`k_Q → k_q`; the key point in its construction is that `adicCompletionMap` maps the maximal ideal
of `Q.adicCompletionIntegers K` into the maximal ideal of `q.adicCompletionIntegers L`
(`adicCompletionMap_val_lt_one`). -/

/-- The local homomorphism of integer rings induced by `adicCompletionMap`. -/
noncomputable def intCompletionMap {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Q.adicCompletionIntegers K →+* q.adicCompletionIntegers L where
  toFun x := ⟨Commons.RingTheory.Henselian.adicCompletionMap Q q hq (x : Q.adicCompletion K),
    Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)

lemma intCompletionMap_coe {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : Q.adicCompletionIntegers K) :
    ((intCompletionMap Q q hq x : q.adicCompletionIntegers L) : q.adicCompletion L) =
      Commons.RingTheory.Henselian.adicCompletionMap Q q hq (x : Q.adicCompletion K) := rfl

/-- `adicCompletionMap` maps the maximal ideal of the integers of `K_Q` into the maximal ideal of
the integers of `L_q`. -/
lemma intCompletionMap_mem_maximalIdeal {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) {x : Q.adicCompletionIntegers K}
    (hx : x ∈ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :
    intCompletionMap Q q hq x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
  rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one]
  have hx' := (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
    Q x).mp hx
  have h := Commons.RingTheory.Henselian.adicCompletionMap_val_lt_one Q q hq hx'
  rw [show ((intCompletionMap Q q hq x : q.adicCompletionIntegers L) : q.adicCompletion L) =
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq (x : Q.adicCompletion K) from
      intCompletionMap_coe Q q hq x]
  exact h

/-- The natural ring homomorphism `k_Q → k_q` between the residue fields of the two adic
completions. -/
noncomputable def natResidueMap {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    IsLocalRing.ResidueField (Q.adicCompletionIntegers K) →+*
      IsLocalRing.ResidueField (q.adicCompletionIntegers L) :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
    ((IsLocalRing.residue (q.adicCompletionIntegers L)).comp (intCompletionMap Q q hq))
    (fun _ ha => by
      rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
      exact intCompletionMap_mem_maximalIdeal Q q hq ha)

lemma natResidueMap_residue {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (a : Q.adicCompletionIntegers K) :
    natResidueMap Q q hq (IsLocalRing.residue (Q.adicCompletionIntegers K) a) =
      IsLocalRing.residue (q.adicCompletionIntegers L) (intCompletionMap Q q hq a) :=
  Ideal.Quotient.lift_mk _ _ _

lemma natResidueMap_injective {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Function.Injective (natResidueMap Q q hq) :=
  RingHom.injective _

/-- **Two ring homomorphisms from a finite field into a field have the same range.**

Let `k` be a finite field and `R` a field.  Then any two ring homomorphisms `k →+* R` have the
same image, namely the unique subfield of `R` with `#k` elements (which may fail to exist, in
which case there are no such homomorphisms at all). -/
theorem ringHom_range_eq_of_finite_field {k R : Type*} [Field k] [Fintype k] [Field R]
    (f g : k →+* R) : f.range = g.range := by
  set q := Fintype.card k with hq
  have hqne : q ≠ 1 := by
    have := Fintype.one_lt_card (α := k); omega
  have hq1 : 1 ≤ q := by
    have := Fintype.card_pos (α := k); omega
  have hp : (X ^ q - X : R[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : R[X] => Polynomial.coeff p q) h
    rw [Polynomial.coeff_sub, Polynomial.coeff_zero, Polynomial.coeff_X_pow_self,
      Polynomial.coeff_X_of_ne_one hqne, sub_zero] at hc
    exact one_ne_zero hc
  have haeval : ∀ x : R, Polynomial.aeval x (X ^ q - X : R[X]) = x ^ q - x := by
    intro x
    simp [Polynomial.aeval_def]
  have hmem : ∀ x : R, x ∈ (X ^ q - X : R[X]).rootSet R ↔ x ^ q = x := by
    intro x
    rw [Polynomial.mem_rootSet, haeval x]
    exact ⟨fun h => sub_eq_zero.mp h.2, fun h => ⟨hp, sub_eq_zero.mpr h⟩⟩
  have hZeq : ({x : R | x ^ q = x} : Set R) = (X ^ q - X : R[X]).rootSet R := by
    ext x; exact (hmem x).symm
  have hZfin : ({x : R | x ^ q = x} : Set R).Finite := by
    rw [hZeq]; exact Polynomial.rootSet_finite _ R
  have hZbound : ({x : R | x ^ q = x} : Set R).ncard ≤ q := by
    rw [hZeq]
    calc ((X ^ q - X : R[X]).rootSet R).ncard
        ≤ (X ^ q - X : R[X]).natDegree := Polynomial.ncard_rootSet_le _ R
      _ ≤ max (X ^ q : R[X]).natDegree (X : R[X]).natDegree := Polynomial.natDegree_sub_le _ _
      _ = q := by simp [Nat.max_eq_left hq1]
  have key : ∀ h : k →+* R, (h.range : Set R) = {x : R | x ^ q = x} := by
    intro h
    have hle : (h.range : Set R) ⊆ {x : R | x ^ q = x} := by
      rintro x ⟨y, rfl⟩
      change (h y) ^ q = h y
      rw [← map_pow, FiniteField.pow_card]
    have hcard : (h.range : Set R).ncard = q := by
      have hinj : Function.Injective h := RingHom.injective h
      have h1 : (h.range : Set R) = h '' Set.univ := by
        ext x; simp
      rw [h1, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_eq_fintype_card]
    exact Set.eq_of_subset_of_ncard_le hle (by rw [hcard]; exact hZbound) hZfin
  refine Subring.ext fun x => ?_
  show x ∈ (f.range : Set R) ↔ x ∈ (g.range : Set R)
  rw [key f, key g]

/-- **The subgroup of ring automorphisms of `R` fixing the image of `φ` pointwise.** -/
def fixSubgroup {S R : Type*} [Semiring S] [Semiring R] (φ : S →+* R) : Subgroup (RingAut R) where
  carrier := {α | ∀ a : S, α (φ a) = φ a}
  mul_mem' := fun {α β} hα hβ a => by
    simp only [Set.mem_ofPred_eq] at hα hβ ⊢
    rw [show (α * β) (φ a) = α (β (φ a)) from rfl, hβ, hα]
  one_mem' := fun a => rfl
  inv_mem' := fun {α} hα a => by
    have h : α⁻¹ (α (φ a)) = α⁻¹ (φ a) := congrArg (fun z => α⁻¹ z) (hα a)
    simpa using h.symm

/-- The subgroup of `RingAut R` fixing `φ`'s image pointwise is the group of `S`-algebra
automorphisms of `R`, for the `S`-algebra structure induced by `φ`. -/
noncomputable def fixSubgroupMulEquiv {S R : Type*} [CommSemiring S] [CommSemiring R]
    (φ : S →+* R) :
    letI : Algebra S R := φ.toAlgebra
    fixSubgroup φ ≃* (R ≃ₐ[S] R) := by
  letI : Algebra S R := φ.toAlgebra
  refine
  { toFun := fun α => AlgEquiv.ofRingEquiv (f := (α : RingAut R)) (fun x => α.2 x)
    invFun := fun β => ⟨(β : R ≃+* R), fun a => β.commutes a⟩
    left_inv := fun α => Subtype.ext rfl
    right_inv := fun β => AlgEquiv.ext fun x => rfl
    map_mul' := fun α β => AlgEquiv.ext fun x => rfl }

/-- **The number of `S`-algebra automorphisms of the residue field of an adic completion is the
inertia degree.**  Here `S` is the residue field of `Q.adicCompletionIntegers K` embedded in the
residue field `R` of `q.adicCompletionIntegers L` by an arbitrary *injective* ring homomorphism
`φ`; the extension `R / S` of finite fields is then Galois with `[R : S] = f(q|Q)`. -/
theorem natCard_algEquiv_residueField_eq_inertiaDeg_of_injective {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (φ : IsLocalRing.ResidueField (Q.adicCompletionIntegers K) →+*
        IsLocalRing.ResidueField (q.adicCompletionIntegers L))
    (hφ : Function.Injective φ) :
    (letI := φ.toAlgebra
     Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L) ≃ₐ[
         IsLocalRing.ResidueField (Q.adicCompletionIntegers K)]
       IsLocalRing.ResidueField (q.adicCompletionIntegers L)) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  letI := φ.toAlgebra
  let ResK := IsLocalRing.ResidueField (Q.adicCompletionIntegers K)
  let ResL := IsLocalRing.ResidueField (q.adicCompletionIntegers L)
  change Nat.card (ResL ≃ₐ[ResK] ResL) = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)
  haveI hK : Finite ResK := finite_residueField_adicCompletion K Q
  haveI hL : Finite ResL := finite_residueField_adicCompletion L q
  have hcard : Nat.card (ResL ≃ₐ[ResK] ResL) = Module.finrank ResK ResL :=
    IsGalois.card_aut_eq_finrank (F := ResK) (E := ResL)
  have hpow : Nat.card ResL = Nat.card ResK ^ Module.finrank ResK ResL :=
    Module.natCard_eq_pow_finrank (K := ResK) (V := ResL)
  have hpow' : Nat.card ResL =
      Nat.card ResK ^ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    natCard_residueField_adicCompletion_eq_pow_inertiaDeg K L Q q hq
  have hbase : 2 ≤ Nat.card ResK := Finite.one_lt_card
  have hfin : Module.finrank ResK ResL = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    Nat.pow_right_injective hbase (hpow.symm.trans hpow')
  rw [hcard, hfin]

theorem exists_ringEquiv_adicCompletion_of_residue_ringEquiv {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (φ : IsLocalRing.ResidueField (Q.adicCompletionIntegers K) →+*
        IsLocalRing.ResidueField (q.adicCompletionIntegers L))
    (hφ : Function.Injective φ)
    (τ : IsLocalRing.ResidueField (q.adicCompletionIntegers L) ≃+*
        IsLocalRing.ResidueField (q.adicCompletionIntegers L))
    (hτ : ∀ a : IsLocalRing.ResidueField (Q.adicCompletionIntegers K), τ (φ a) = φ a) :
    ∃ σ : q.adicCompletion L ≃+* q.adicCompletion L,
      (∀ y : Q.adicCompletion K,
        σ (Commons.RingTheory.Henselian.adicCompletionMap Q q hq y) =
          Commons.RingTheory.Henselian.adicCompletionMap Q q hq y) ∧
      ∀ (x : q.adicCompletionIntegers L)
        (hx : σ (x : q.adicCompletion L) ∈ q.adicCompletionIntegers L),
        τ (IsLocalRing.residue (q.adicCompletionIntegers L) x) =
          IsLocalRing.residue (q.adicCompletionIntegers L) ⟨σ (x : q.adicCompletion L), hx⟩ := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  let A := Q.adicCompletionIntegers K
  let B := q.adicCompletionIntegers L
  let KK := Q.adicCompletion K
  let LL := q.adicCompletion L
  let ResK := IsLocalRing.ResidueField A
  let ResL := IsLocalRing.ResidueField B
  haveI hKfin : Finite ResK := finite_residueField_adicCompletion K Q
  haveI hLfin : Finite ResL := finite_residueField_adicCompletion L q
  haveI hKft : Fintype ResK := Fintype.ofFinite ResK
  -- the inertia subgroup of the local Galois group
  obtain ⟨I, hI, hIcard⟩ := exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx Q q hq
  -- a `K_Q`-algebra automorphism of `L_q` preserves the ring of integers
  have hpres : ∀ (σ : LL ≃ₐ[KK] LL) (y : LL), σ y ∈ B ↔ y ∈ B :=
    fun σ y => algEquiv_mem_adicCompletionIntegers_iff_adicCompletion Q q hq σ y
  -- hence restricts to a ring automorphism of `B`
  let restr : (LL ≃ₐ[KK] LL) → B ≃+* B := fun σ =>
    { toFun := fun x => ⟨σ (x : LL), (hpres σ (x : LL)).mpr x.2⟩
      invFun := fun y => ⟨σ.symm (y : LL), (hpres σ.symm (y : LL)).mpr y.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have restr_coe : ∀ (σ : LL ≃ₐ[KK] LL) (x : B), ((restr σ x : B) : LL) = σ (x : LL) :=
    fun _ _ => rfl
  have restr_sub_coe : ∀ (σ : LL ≃ₐ[KK] LL) (x : B),
      ((restr σ x - x : B) : LL) = σ (x : LL) - (x : LL) := by
    intro σ x
    simp [restr_coe]
  have restr_one : restr 1 = 1 := by
    refine RingEquiv.ext fun x => Subtype.ext ?_
    rw [restr_coe]
    exact AlgEquiv.one_apply (x : LL)
  have restr_mul : ∀ σ σ' : LL ≃ₐ[KK] LL, restr (σ * σ') = restr σ * restr σ' := by
    intro σ σ'
    refine RingEquiv.ext fun x => Subtype.ext ?_
    change ((restr (σ * σ')) x : LL) = ((restr σ) ((restr σ') x) : LL)
    rw [restr_coe, restr_coe, restr_coe, AlgEquiv.mul_apply]
  let restrHom : (LL ≃ₐ[KK] LL) →* RingAut B :=
    { toFun := restr, map_one' := restr_one, map_mul' := restr_mul }
  -- the induced action on the residue field
  let ρ : (LL ≃ₐ[KK] LL) →* RingAut ResL :=
    (IsLocalRing.ResidueField.mapAut : RingAut B →* RingAut ResL).comp restrHom
  have ρ_apply_residue : ∀ (σ : LL ≃ₐ[KK] LL) (x : B),
      ρ σ (IsLocalRing.residue B x) = IsLocalRing.residue B (restr σ x) := by
    intro σ x
    show IsLocalRing.ResidueField.mapAut (restrHom σ) (IsLocalRing.residue B x) =
      IsLocalRing.residue B (restr σ x)
    rw [IsLocalRing.ResidueField.mapAut_apply, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  -- the kernel of `ρ` is the inertia subgroup
  have hker : ρ.ker = I := by
    ext σ
    rw [MonoidHom.mem_ker, hI]
    constructor
    · intro h x
      have hx : IsLocalRing.residue B (restr σ x) = IsLocalRing.residue B x := by
        rw [← ρ_apply_residue σ x, h]; rfl
      have hzero : IsLocalRing.residue B (restr σ x - x) = 0 := by
        rw [map_sub, hx, sub_self]
      have hmem : restr σ x - x ∈ IsLocalRing.maximalIdeal B :=
        (IsLocalRing.residue_eq_zero_iff _).mp hzero
      have hval := (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
        q (restr σ x - x)).mp hmem
      rwa [restr_sub_coe] at hval
    · intro h
      refine RingEquiv.ext fun r => ?_
      show ρ σ r = r
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
      rw [ρ_apply_residue σ x]
      have hzero : IsLocalRing.residue B (restr σ x - x) = 0 := by
        rw [map_sub]
        have hmem : restr σ x - x ∈ IsLocalRing.maximalIdeal B := by
          refine (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
            q _).mpr ?_
          rw [restr_sub_coe]
          exact h x
        exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
      have hsub : IsLocalRing.residue B (restr σ x) - IsLocalRing.residue B x = 0 := by
        simpa using hzero
      exact sub_eq_zero.mp hsub
  -- the cardinality of the range of `ρ`
  have hGcard : Nat.card (LL ≃ₐ[KK] LL) =
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq
  have hrange : Nat.card ρ.range = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    have h1 : Nat.card ((LL ≃ₐ[KK] LL) ⧸ ρ.ker) * Nat.card ρ.ker = Nat.card (LL ≃ₐ[KK] LL) := by
      simpa only [Subgroup.index_eq_card] using Subgroup.index_mul_card ρ.ker
    rw [hker, hIcard, hGcard] at h1
    have he : 0 < q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
      Ideal.ramificationIdx_pos (NumberField.RingOfIntegers K) q.asIdeal
    have h2 : Nat.card ((LL ≃ₐ[KK] LL) ⧸ I) =
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
      rw [mul_comm (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K))
        (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))] at h1
      exact Nat.mul_right_cancel he h1
    have h3 : Nat.card ((LL ≃ₐ[KK] LL) ⧸ ρ.ker) = Nat.card ρ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    rw [← h3, hker, h2]
  -- the natural map of residue fields
  let ψ : ResK →+* ResL := natResidueMap Q q hq
  have hψinj : Function.Injective ψ := natResidueMap_injective Q q hq
  have hcardFix : Nat.card (fixSubgroup ψ) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    have h := natCard_algEquiv_residueField_eq_inertiaDeg_of_injective Q q hq ψ hψinj
    rw [Nat.card_congr (fixSubgroupMulEquiv ψ).toEquiv]
    exact h
  -- the range of `ρ` is exactly the group of automorphisms of `ResL` fixing `ψ`'s image
  have hle : ρ.range ≤ fixSubgroup ψ := by
    rintro α ⟨σ, rfl⟩ a
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a
    rw [natResidueMap_residue, ρ_apply_residue]
    congr 1
    exact Subtype.ext (by rw [restr_coe, intCompletionMap_coe]; exact σ.commutes (x : KK))
  have hfixeq : ρ.range = fixSubgroup ψ := by
    haveI : Finite (RingAut ResL) := by
      haveI : Finite (ResL → ResL) := inferInstance
      exact Finite.of_injective (fun f : RingAut ResL => (f : ResL → ResL))
        (fun f g h => by ext x; exact congrFun h x)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hcardFix])
  -- `τ` fixes the image of `φ`, and `φ` and `ψ` have the same image
  have hfixτ : τ ∈ fixSubgroup ψ := by
    intro a
    have hmem : ψ a ∈ φ.range := by
      rw [← ringHom_range_eq_of_finite_field ψ φ]
      exact ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hmem
    rw [← hb, hτ b]
  have hτmem : τ ∈ ρ.range := by rw [hfixeq]; exact hfixτ
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hτmem
  refine ⟨(σ : LL ≃+* LL), ?_, ?_⟩
  · intro y
    rw [← RingHom.algebraMap_toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)]
    exact σ.commutes y
  · intro x hx
    have h1 : ρ σ (IsLocalRing.residue B x) = IsLocalRing.residue B (restr σ x) :=
      ρ_apply_residue σ x
    have h2 : τ (IsLocalRing.residue B x) = IsLocalRing.residue B (restr σ x) := by
      rw [← hσ]; exact h1
    rw [h2]
    congr 1

end Commons.NumberTheory.NumberField.Completion

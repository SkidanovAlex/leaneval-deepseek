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
import Submission.Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq
import Submission.Commons.Analysis.Nonarchimedean.val_pow_sub_one_le_exp_neg
import Submission.Commons.GroupTheory.SpecificGroups.Cyclic.card_quotient_powMonoidHom
import Submission.Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_pow_mul_eq_int_adicCompletion_rat
import Submission.Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_adicCompletion_iff
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial
import Submission.Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_residueClass
import Submission.Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField
open scoped WithZero
open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## A general group-theoretic cardinality computation

For a surjective homomorphism `φ : G →* H` of commutative groups with no nontrivial `n`-torsion
in `H`, the quotient of `G` by its `n`-th powers decomposes as the product of the quotient of `H`
by its `n`-th powers and the quotient of `ker φ` by its `n`-th powers. -/

theorem natCard_quot_powMonoidHom_eq_mul {G H : Type*} [CommGroup G] [CommGroup H]
    (φ : G →* H) (hφ : Function.Surjective φ) (n : ℕ) [NeZero n]
    (htor : ∀ h : H, h ^ n = 1 → h = 1) :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card (H ⧸ (powMonoidHom n : H →* H).range) *
        Nat.card (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range) := by
  let R : Subgroup G := (powMonoidHom n : G →* G).range
  have hKR : R.subgroupOf φ.ker = (powMonoidHom n : φ.ker →* φ.ker).range := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hx
      simp only [powMonoidHom_apply] at hg
      have hpg : φ g ^ n = 1 := by
        have hx1 : φ (x : G) = 1 := x.2
        rw [← map_pow, hg, hx1]
      have hgK : φ g = 1 := htor (φ g) hpg
      exact MonoidHom.mem_range.mpr ⟨⟨g, hgK⟩, Subtype.ext hg⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hx
      rw [← hk]
      exact MonoidHom.mem_range.mpr ⟨(k : G), by rfl⟩
  have hmap : (φ.ker ⊔ R).map φ = (powMonoidHom n : H →* H).range := by
    rw [Subgroup.map_sup]
    have hKmap : (φ.ker).map φ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
    have hRmap : R.map φ = (powMonoidHom n : H →* H).range := by
      show ((powMonoidHom n : G →* G).range).map φ = _
      rw [MonoidHom.map_range]
      ext y
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨φ g, by rw [← hg]; simp only [MonoidHom.comp_apply, powMonoidHom_apply, map_pow]⟩
      · rintro ⟨h, hh⟩
        obtain ⟨g, rfl⟩ := hφ h
        exact ⟨g, by rw [MonoidHom.comp_apply, powMonoidHom_apply, map_pow, ← hh, powMonoidHom_apply]⟩
    rw [hKmap, hRmap, bot_sup_eq]
  have h1 : (φ.ker ⊔ R : Subgroup G).index = (powMonoidHom n : H →* H).range.index := by
    have hS := Subgroup.index_map_eq (φ.ker ⊔ R : Subgroup G) hφ
      (le_sup_left : φ.ker ≤ (φ.ker ⊔ R : Subgroup G))
    rw [hmap] at hS
    exact hS.symm
  have h2 : R.relIndex (φ.ker ⊔ R : Subgroup G)
      = Nat.card (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range) := by
    show Nat.card ((φ.ker ⊔ R : Subgroup G) ⧸ R.subgroupOf (φ.ker ⊔ R)) = _
    rw [← Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient φ.ker R).toEquiv]
    rw [hKR]
  calc Nat.card (G ⧸ R) = R.index := rfl
    _ = R.relIndex (φ.ker ⊔ R : Subgroup G) * (φ.ker ⊔ R : Subgroup G).index :=
        (Subgroup.relIndex_mul_index (le_sup_right : R ≤ (φ.ker ⊔ R : Subgroup G))).symm
    _ = R.relIndex (φ.ker ⊔ R : Subgroup G) * (powMonoidHom n : H →* H).range.index := by rw [h1]
    _ = Nat.card (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range) *
          (powMonoidHom n : H →* H).range.index := by rw [h2]
    _ = Nat.card (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range) *
          Nat.card (H ⧸ (powMonoidHom n : H →* H).range) := rfl
    _ = Nat.card (H ⧸ (powMonoidHom n : H →* H).range) *
          Nat.card (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range) := by ring


/-- The predicate "every element of `1 + 𝔪 ^ k` is a `p`-th power of an element of `1 + 𝔪`",
formulated for a valued field `F` with value group `ℤᵐ⁰`. -/
def PpowRat (F : Type*) [Field F] (vv : Valuation F Zstar0) (p : ℕ) (k : ℕ) : Prop :=
  ∀ u : F, vv (u - 1) ≤ WithZero.exp (-(k : ℤ)) →
    ∃ y : F, vv (y - 1) ≤ WithZero.exp (-1) ∧ y ^ p = u

theorem powQuotRat_exp_neg_lt_one {n : ℕ} (hn : 1 ≤ n) :
    (WithZero.exp (-(n:ℤ)) : Zstar0) < 1 := by
  have h : WithZero.exp (-(n:ℤ)) < WithZero.exp (0:ℤ) := by
    rw [WithZero.exp_lt_exp]; omega
  simpa using h

theorem powQuotRat_val_eq_one_of_val_sub_one_lt_one {F : Type*} [Field F]
    (vv : Valuation F Zstar0) {x : F} (h : vv (x - 1) < 1) : vv x = 1 := by
  have h' := Valuation.map_add_eq_of_lt_left vv (x := (1:F)) (y := x - 1) (by simpa using h)
  rwa [show (1:F) + (x-1) = x by ring, Valuation.map_one] at h'

theorem powQuotRat_val_natCast_le_exp_neg_one {F : Type*} [Field F] (vv : Valuation F Zstar0)
    {p n : ℕ} (hvalp : vv ((p : ℕ) : F) = WithZero.exp (-1 : ℤ)) (hdvd : p ∣ n) :
    vv ((n : ℕ) : F) ≤ WithZero.exp (-1 : ℤ) := by
  obtain ⟨m, rfl⟩ := hdvd
  rw [Nat.cast_mul, Valuation.map_mul, hvalp]
  calc WithZero.exp (-1:ℤ) * vv ((m:ℕ):F)
      ≤ WithZero.exp (-1:ℤ) * 1 :=
        mul_le_mul' (le_refl _) (Commons.Analysis.Nonarchimedean.val_natCast_le_one vv m)
    _ = WithZero.exp (-1:ℤ) := mul_one _

theorem powQuotRat_pow_le_exp {F : Type*} [Field F] (vv : Valuation F Zstar0) {x : F} {a : ℤ}
    (hx : vv x ≤ WithZero.exp a) (n : ℕ) :
    vv (x^n) ≤ WithZero.exp ((n:ℤ) * a) := by
  rw [Valuation.map_pow]
  calc vv x ^ n ≤ (WithZero.exp a)^n := pow_le_pow_left' hx n
    _ = WithZero.exp ((n:ℤ) * a) := by
        rw [← WithZero.exp_nsmul, nsmul_eq_mul]

theorem powQuotRat_mul_pow_le_exp {F : Type*} [Field F] (vv : Valuation F Zstar0)
    {x y : F} {a b : ℤ} (hx : vv x ≤ WithZero.exp a) (hy : vv y ≤ WithZero.exp b) (n : ℕ) :
    vv (x^n * y) ≤ WithZero.exp ((n:ℤ) * a + b) := by
  rw [Valuation.map_mul]
  calc vv (x^n) * vv y ≤ WithZero.exp ((n:ℤ)*a) * WithZero.exp b :=
        mul_le_mul' (powQuotRat_pow_le_exp vv hx n) hy
    _ = WithZero.exp ((n:ℤ)*a + b) := (WithZero.exp_add _ _).symm

/-- Base case of the bootstrap: `1 + 𝔪 ^ (M+1)` is contained in the `p`-th powers of
`1 + 𝔪`, where `M` is the depth of the `p`-adic logarithm. -/
theorem powQuotRat_base {F : Type*} [Field F] (vv : Valuation F Zstar0) (p M : ℕ)
    (hp : p.Prime) (hp0 : ((p:ℕ):F) ≠ 0)
    (hM : 1 ≤ M) (exp log : F → F)
    (hexp0 : exp 0 = 1)
    (hexpm1 : ∀ x : F, vv x ≤ WithZero.exp (-(M:ℤ)) → vv (exp x - 1) = vv x)
    (hexpadd : ∀ x y : F, vv x ≤ WithZero.exp (-(M:ℤ)) → vv y ≤ WithZero.exp (-(M:ℤ)) →
      exp (x + y) = exp x * exp y)
    (hlogval : ∀ y : F, vv (y - 1) ≤ WithZero.exp (-(M:ℤ)) → vv (log y) = vv (y-1))
    (hloginv : ∀ y : F, vv (y - 1) ≤ WithZero.exp (-(M:ℤ)) → exp (log y) = y)
    (hvalp : vv ((p : ℕ) : F) = WithZero.exp (-1 : ℤ)) :
    PpowRat F vv p (M + 1) := by
  intro u hu
  by_cases hu1 : u = 1
  · refine ⟨1, ?_, ?_⟩
    · rw [sub_self, map_zero]; exact bot_le
    · rw [hu1]; exact one_pow p
  have hle1 : WithZero.exp (-(M:ℤ)) ≤ (WithZero.exp (-1 : ℤ) : Zstar0) := by
    rw [WithZero.exp_le_exp]; omega
  have huM : vv (u - 1) ≤ WithZero.exp (-(M:ℤ)) := by
    refine le_trans hu ?_
    rw [WithZero.exp_le_exp]; push_cast; omega
  have hlt1 : vv (u - 1) < (1 : Zstar0) := by
    refine lt_of_le_of_lt huM ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hvalu : vv u = 1 := powQuotRat_val_eq_one_of_val_sub_one_lt_one vv (by simpa using hlt1)
  set z : F := log u / ((p:ℕ):F) with hzdef
  have hzval : vv z ≤ WithZero.exp (-(M:ℤ)) := by
    rw [hzdef, Valuation.map_div, hlogval u huM, hvalp, div_eq_mul_inv]
    have h1 : (WithZero.exp (-1 : ℤ))⁻¹ = (WithZero.exp (1 : ℤ) : Zstar0) := by
      rw [← WithZero.exp_neg]; norm_num
    rw [h1]
    calc vv (u - 1) * WithZero.exp (1 : ℤ)
        ≤ WithZero.exp (-((M+1:ℕ):ℤ)) * WithZero.exp (1 : ℤ) :=
          mul_le_mul' hu (le_refl _)
      _ = WithZero.exp (-(M:ℤ)) := by
          rw [← WithZero.exp_add]; congr 1; push_cast; ring
  have hdisk : ∀ m : ℕ, vv ((m:ℕ) • z) ≤ WithZero.exp (-(M:ℤ)) := by
    intro m
    rw [nsmul_eq_mul, Valuation.map_mul]
    calc vv ((m:ℕ):F) * vv z ≤ 1 * WithZero.exp (-(M:ℤ)) :=
          mul_le_mul' (Commons.Analysis.Nonarchimedean.val_natCast_le_one vv m) hzval
      _ = WithZero.exp (-(M:ℤ)) := one_mul _
  have hpow_exp : ∀ m : ℕ, exp ((m:ℕ) • z) = (exp z)^m := by
    intro m; induction m with
    | zero => rw [zero_nsmul, hexp0, pow_zero]
    | succ m ih =>
      rw [succ_nsmul, hexpadd _ _ (hdisk m) hzval, ih, pow_succ]
  have hzlog : (p:ℕ) • z = log u := by
    rw [hzdef, nsmul_eq_mul]
    field_simp
  refine ⟨exp z, ?_, ?_⟩
  · rw [hexpm1 z hzval]
    exact le_trans hzval hle1
  · rw [← hpow_exp p, hzlog, hloginv u huM]

/-- One bootstrap step: if `1 + 𝔪 ^ (k+1)` is contained in the `p`-th powers of `1 + 𝔪`,
then so is `1 + 𝔪 ^ k`.  The correction term in Newton's method is small enough because the
binomial coefficients `C(p,j)` for `2 ≤ j ≤ p-1` are divisible by `p`. -/
theorem powQuotRat_step {F : Type*} [Field F] (vv : Valuation F Zstar0) (p k : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2) (hk : 2 ≤ k) (hp0 : ((p:ℕ):F) ≠ 0)
    (hvalp : vv ((p : ℕ) : F) = WithZero.exp (-1 : ℤ))
    (hP : PpowRat F vv p (k+1)) :
    PpowRat F vv p k := by
  intro u hu
  by_cases hu1 : u = 1
  · refine ⟨1, ?_, ?_⟩
    · rw [sub_self, map_zero]; exact bot_le
    · rw [hu1]; exact one_pow p
  set t : F := (u - 1) / ((p:ℕ):F) with htdef
  have htval : vv t ≤ WithZero.exp (-(k:ℤ) + 1) := by
    rw [htdef, Valuation.map_div, hvalp, div_eq_mul_inv]
    have h1 : (WithZero.exp (-1 : ℤ))⁻¹ = (WithZero.exp (1 : ℤ) : Zstar0) := by
      rw [← WithZero.exp_neg]; norm_num
    rw [h1]
    calc vv (u - 1) * WithZero.exp (1:ℤ)
        ≤ WithZero.exp (-(k:ℤ)) * WithZero.exp (1:ℤ) := mul_le_mul' hu (le_refl _)
      _ = WithZero.exp (-(k:ℤ) + 1) := by rw [← WithZero.exp_add]
  have htk : WithZero.exp (-(k:ℤ) + 1) ≤ (WithZero.exp (-1:ℤ) : Zstar0) := by
    rw [WithZero.exp_le_exp]; omega
  have htval1 : vv t ≤ WithZero.exp (-1 : ℤ) := le_trans htval htk
  have hpt : ((p:ℕ):F) * t = u - 1 := by
    rw [htdef]; field_simp
  set y0 : F := 1 + t with hy0def
  have hy0val : vv (y0 - 1) ≤ WithZero.exp (-1 : ℤ) := by
    rw [hy0def]
    have : (1:F) + t - 1 = t := by ring
    rw [this]; exact htval1
  have hy0one : vv y0 = 1 := by
    have hlt : vv (y0 - 1) < (1:Zstar0) := lt_of_le_of_lt hy0val (powQuotRat_exp_neg_lt_one le_rfl)
    exact powQuotRat_val_eq_one_of_val_sub_one_lt_one vv hlt
  have hident : (1 + t)^p - u
      = ∑ j ∈ Finset.range (p-1), t^(j+2) * ((p.choose (j+2) : ℕ) : F) := by
    have hbin := Commons.Analysis.Nonarchimedean.val_pow_sub_one_binomial_split t hp.one_le
    have hrw : (1 + t)^p - u = ((1+t)^p - 1) + (1 - u) := by ring
    rw [hrw, hbin, hpt]; ring
  have hE : vv ((1 + t)^p - u) ≤ WithZero.exp (-(k:ℤ) - 1) := by
    rw [hident]
    apply Valuation.map_sum_le
    intro j hj
    rw [Finset.mem_range] at hj
    have hjp : j + 2 ≤ p := by omega
    rcases lt_or_eq_of_le hjp with hlt | heq
    · have hdvd : p ∣ p.choose (j+2) := hp.dvd_choose_self (by omega) hlt
      have hC : vv (((p.choose (j+2) : ℕ)) : F) ≤ WithZero.exp (-1:ℤ) :=
        powQuotRat_val_natCast_le_exp_neg_one vv hvalp hdvd
      calc vv (t^(j+2) * ((p.choose (j+2) : ℕ) : F))
          ≤ WithZero.exp (((j+2:ℕ):ℤ) * (-(k:ℤ)+1) + (-1)) :=
            powQuotRat_mul_pow_le_exp vv htval hC (j+2)
        _ ≤ WithZero.exp (-(k:ℤ) - 1) := by
            rw [WithZero.exp_le_exp]
            have hj0 : (0:ℤ) ≤ (j:ℤ) := Int.natCast_nonneg j
            have hk2 : (2:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
            push_cast
            nlinarith
    · have hC1 : ((p.choose (j+2) : ℕ) : F) = 1 := by rw [heq, Nat.choose_self]; norm_num
      rw [hC1, mul_one]
      calc vv (t^(j+2)) ≤ WithZero.exp (((j+2:ℕ):ℤ) * (-(k:ℤ)+1)) :=
            powQuotRat_pow_le_exp vv htval (j+2)
        _ ≤ WithZero.exp (-(k:ℤ) - 1) := by
            rw [WithZero.exp_le_exp]
            have hjp' : ((j+2 : ℕ) : ℤ) = (p:ℤ) := by rw [heq]
            have hp3 : (3:ℤ) ≤ (p:ℤ) := by
              have h2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
              exact_mod_cast h2
            have hk2 : (2:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
            rw [hjp']
            nlinarith
  have huone : vv u = 1 := by
    refine powQuotRat_val_eq_one_of_val_sub_one_lt_one vv ?_
    refine lt_of_le_of_lt hu ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hune : u ≠ 0 := (Valuation.ne_zero_iff vv).mp (by rw [huone]; exact one_ne_zero)
  set w : F := (1+t)^p / u with hwdef
  have hwval : vv (w - 1) ≤ WithZero.exp (-((k+1:ℕ):ℤ)) := by
    have hw : w - 1 = ((1+t)^p - u) / u := by
      rw [hwdef]; field_simp
    rw [hw, Valuation.map_div, huone, div_one]
    refine le_trans hE (le_of_eq ?_)
    congr 1; push_cast; ring
  obtain ⟨w₀, hw0val, hw0pow⟩ := hP w hwval
  have hw0one : vv w₀ = 1 := by
    have hlt : vv (w₀ - 1) < (1:Zstar0) := lt_of_le_of_lt hw0val (powQuotRat_exp_neg_lt_one le_rfl)
    exact powQuotRat_val_eq_one_of_val_sub_one_lt_one vv hlt
  have hw0ne : w₀ ≠ 0 := (Valuation.ne_zero_iff vv).mp (by rw [hw0one]; exact one_ne_zero)
  refine ⟨y0 / w₀, ?_, ?_⟩
  · have hyw : y0 / w₀ - 1 = (y0 - w₀)/w₀ := by field_simp
    rw [hyw, Valuation.map_div, hw0one, div_one]
    have heq2 : y0 - w₀ = (y0 - 1) - (w₀ - 1) := by ring
    rw [heq2]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · exact hy0val
    · exact hw0val
  · have h1tne : (1 + t) ≠ 0 := by
      intro h
      have hh := hy0one
      rw [hy0def, h] at hh
      simp at hh
    rw [div_pow, hy0def, hw0pow, hwdef]
    field_simp

/-- **The key `p`-adic root statement.**  If `p` is an odd prime which is a uniformizer of the
valued field `F` (i.e. `vv p = exp (-1)`), then every element of `1 + 𝔪 ^ 2` is a `p`-th power of
an element of `1 + 𝔪`. -/
theorem powQuotRat_crux (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0) ((p : ℚ) : v.adicCompletion ℚ)
      = WithZero.exp (-1 : ℤ)) :
    PpowRat (v.adicCompletion ℚ) (Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)) p 2 := by
  obtain ⟨M, hM1, exp, log, hexpsum, hexpm1, hexp0, hexpadd, hlog, hlogexp⟩ :=
    Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq v
  have hvalp' : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0) ((p:ℕ) : v.adicCompletion ℚ) = WithZero.exp (-1:ℤ) := by
    rw [show ((p:ℕ) : v.adicCompletion ℚ) = ((p:ℚ) : v.adicCompletion ℚ) by push_cast; rfl]
    exact hvalp
  have hp0 : ((p:ℕ) : v.adicCompletion ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mp (by rw [hvalp']; exact WithZero.exp_ne_zero)
  have hbase : PpowRat (v.adicCompletion ℚ) (Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)) p (M+1) :=
    powQuotRat_base _ p M hp hp0 hM1 exp log hexp0 hexpm1 hexpadd
      (fun y hy => (hlog y hy).2.1) (fun y hy => (hlog y hy).2.2) hvalp'
  exact (Nat.decreasingInduction (n := M+1)
    (motive := fun m _ => 2 ≤ m → PpowRat (v.adicCompletion ℚ)
      (Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)) p m)
    (fun k hk hprev hk2 =>
      powQuotRat_step _ p k hp hodd hk2 hp0 hvalp' (hprev (by omega)))
    (fun _ => hbase)
    (m := 2) (by omega)) (le_refl 2)


/-! ## The map `1 + 𝔪 → κ` recording the "first digit" of a principal unit -/

abbrev piQ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    v.adicCompletionIntegers ℚ :=
  Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers ℚ) (K := ℚ) v

theorem piQ_ne_zero (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    piQ v ≠ 0 :=
  (Commons.RingTheory.Henselian.uniformizer_irreducible
    (R := NumberField.RingOfIntegers ℚ) (K := ℚ) v).ne_zero

theorem maxIdeal_eq_span_piQ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) = Ideal.span {piQ v} :=
  Commons.RingTheory.Henselian.maximalIdeal_eq_span_uniformizer
    (R := NumberField.RingOfIntegers ℚ) (K := ℚ) v

theorem residue_piQ_eq_zero (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    IsLocalRing.residue (v.adicCompletionIntegers ℚ) (piQ v) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, maxIdeal_eq_span_piQ]
  exact Ideal.mem_span_singleton.mpr (dvd_refl _)

abbrev KQ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Subgroup (v.adicCompletionIntegers ℚ)ˣ :=
  (Units.map ((IsLocalRing.residue (v.adicCompletionIntegers ℚ)).toMonoidHom)).ker

theorem thetaCoeff_exists (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : KQ v) :
    ∃ c : v.adicCompletionIntegers ℚ,
      ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1 = piQ v * c := by
  have hmem : ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      ∈ Ideal.span {piQ v} := by
    rw [← maxIdeal_eq_span_piQ v]
    exact (Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_iff
      (u : (v.adicCompletionIntegers ℚ)ˣ)).mp u.2
  exact dvd_def.mp (Ideal.mem_span_singleton.mp hmem)

def thetaCoeff (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (u : KQ v) :
    v.adicCompletionIntegers ℚ := Classical.choose (thetaCoeff_exists v u)

theorem thetaCoeff_spec (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : KQ v) :
    ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      = piQ v * thetaCoeff v u :=
  Classical.choose_spec (thetaCoeff_exists v u)

theorem thetaCoeff_unique (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {u : KQ v} {c : v.adicCompletionIntegers ℚ}
    (h : ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1 = piQ v * c) :
    c = thetaCoeff v u := by
  have h1 := thetaCoeff_spec v u
  have h2 : piQ v * c = piQ v * thetaCoeff v u := by rw [← h, h1]
  exact mul_left_cancel₀ (piQ_ne_zero v) h2

def theta (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (u : KQ v) :
    IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) :=
  IsLocalRing.residue _ (thetaCoeff v u)

theorem theta_mul (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u w : KQ v) : theta v (u * w) = theta v u + theta v w := by
  set c := thetaCoeff v u with hc
  set d := thetaCoeff v w with hd
  have hu : ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
      = 1 + piQ v * c := by rw [hc, ← thetaCoeff_spec v u]; ring
  have hw : ((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
      = 1 + piQ v * d := by rw [hd, ← thetaCoeff_spec v w]; ring
  have hcd : (((u * w : KQ v) : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      = piQ v * (c + d + piQ v * c * d) := by
    rw [show (((u * w : KQ v) : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
        = ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
          * ((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) by simp,
      hu, hw]
    ring
  have hkey : thetaCoeff v (u * w) = c + d + piQ v * c * d := (thetaCoeff_unique v hcd).symm
  simp only [theta, hkey, ← hc, ← hd, map_add, map_mul, residue_piQ_eq_zero]
  ring

def thetaHom (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    KQ v →* Multiplicative (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) where
  toFun u := Multiplicative.ofAdd (theta v u)
  map_one' := by
    have h0 : thetaCoeff v 1 = 0 := by
      have hspec : (((1 : KQ v) : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
          = piQ v * 0 := by simp
      exact (thetaCoeff_unique v hspec).symm
    simp only [theta, h0, map_zero, ofAdd_zero]
  map_mul' u w := by rw [theta_mul]; rfl

theorem thetaHom_apply (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : KQ v) : thetaHom v u = Multiplicative.ofAdd (theta v u) := rfl

theorem theta_surjective (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Function.Surjective (theta v) := by
  intro b
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers ℚ) b
  have hxunit : IsUnit (1 + piQ v * a : v.adicCompletionIntegers ℚ) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add, map_one, map_mul,
      residue_piQ_eq_zero, zero_mul, add_zero]
    exact one_ne_zero
  have hmem : (((hxunit.unit : (v.adicCompletionIntegers ℚ)ˣ)) : v.adicCompletionIntegers ℚ) - 1
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) := by
    rw [IsUnit.unit_spec, maxIdeal_eq_span_piQ]
    have h1 : (1 + piQ v * a : v.adicCompletionIntegers ℚ) - 1 = piQ v * a := by ring
    rw [h1]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  have hker : hxunit.unit ∈ KQ v :=
    (Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_iff hxunit.unit).mpr hmem
  refine ⟨⟨hxunit.unit, hker⟩, ?_⟩
  have hspec : (((⟨hxunit.unit, hker⟩ : KQ v) : (v.adicCompletionIntegers ℚ)ˣ)
      : v.adicCompletionIntegers ℚ) - 1 = piQ v * a := by
    rw [IsUnit.unit_spec]
    ring
  have hcoe : thetaCoeff v ⟨hxunit.unit, hker⟩ = a := (thetaCoeff_unique v hspec).symm
  simp only [theta]
  rw [hcoe, ha]

theorem thetaHom_surjective (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Function.Surjective (thetaHom v) := by
  intro b
  obtain ⟨u, hu⟩ := theta_surjective v (Multiplicative.toAdd b)
  exact ⟨u, by rw [thetaHom_apply, hu, ofAdd_toAdd]⟩

theorem theta_eq_zero_iff (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : KQ v) :
    theta v u = 0 ↔ ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) ^ 2 := by
  simp only [theta]
  rw [IsLocalRing.residue_eq_zero_iff, thetaCoeff_spec v u]
  rw [maxIdeal_eq_span_piQ, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton, dvd_def, dvd_def]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, by rw [hd]; ring⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, mul_left_cancel₀ (piQ_ne_zero v) (by rw [hd]; ring)⟩

/-! ## The `p`-th powers of the principal units -/

theorem KQ_pow_range_le_ker (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (p : ℕ) (hp : p.Prime)
    (hvalpN : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℕ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    (powMonoidHom p : KQ v →* KQ v).range ≤ (thetaHom v).ker := by
  rintro u ⟨w, rfl⟩
  rw [MonoidHom.mem_ker, thetaHom_apply, ofAdd_eq_one, theta_eq_zero_iff]
  have hwmem : ((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) :=
    (Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_iff
      (w : (v.adicCompletionIntegers ℚ)ˣ)).mp w.2
  have hxval : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
        : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ≤ WithZero.exp (-1 : ℤ) := by
    have := (val_le_exp_neg_iff_mem_maximalIdeal_pow v
      (((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1) 1)
    rw [pow_one] at this
    exact this.mpr hwmem
  have hstep := Commons.Analysis.Nonarchimedean.val_pow_sub_one_step
    (Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)) hp.one_le (le_of_eq hvalpN)
    (t := 1) le_rfl hxval
  have hmem2 : (((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) ^ p - 1)
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) ^ 2 := by
    rw [← (val_le_exp_neg_iff_mem_maximalIdeal_pow v
      (((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) ^ p - 1) 2)]
    have hcast : (((((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) ^ p - 1)
        : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
        = (1 + ((((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
            : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) ^ p - 1 := by
      push_cast; ring
    rw [hcast]
    exact hstep
  rw [powMonoidHom_apply]
  rwa [show ((↑(w ^ p : KQ v) : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
      = ((w : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) ^ p by simp]

theorem theta_ker_le_KQ_pow (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    (thetaHom v).ker ≤ (powMonoidHom p : KQ v →* KQ v).range := by
  intro u hu
  rw [MonoidHom.mem_range]
  have hu0 : ((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) ^ 2 := by
    rw [← theta_eq_zero_iff v u, ← ofAdd_eq_one, ← thetaHom_apply]
    exact MonoidHom.mem_ker.mp hu
  have hval2 : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
        : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ≤ WithZero.exp (-2 : ℤ) := by
    have := (val_le_exp_neg_iff_mem_maximalIdeal_pow v
      (((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1) 2).mpr hu0
    simpa using this
  have hcrux := powQuotRat_crux v p hp hodd hvalp
    (((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
    (by simpa using hval2)
  obtain ⟨y, hy1, hyp⟩ := hcrux
  have hylt : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0) (y - 1) < 1 :=
    lt_of_le_of_lt hy1 (powQuotRat_exp_neg_lt_one le_rfl)
  have hyval : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0) y = 1 :=
    powQuotRat_val_eq_one_of_val_sub_one_lt_one _ hylt
  have hymem : y ∈ v.adicCompletionIntegers ℚ :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (NumberField.RingOfIntegers ℚ) ℚ v).mpr (le_of_eq hyval)
  have hyunit : IsUnit (⟨y, hymem⟩ : v.adicCompletionIntegers ℚ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hyval
  have hsubmem : ((hyunit.unit : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) - 1
      ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) := by
    rw [IsUnit.unit_spec]
    have hkey := (val_le_exp_neg_iff_mem_maximalIdeal_pow v (⟨y, hymem⟩ - 1) 1)
    rw [pow_one] at hkey
    exact hkey.mp (by
      rw [show (((⟨y, hymem⟩ : v.adicCompletionIntegers ℚ) - 1
        : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = y - 1 by push_cast; ring]
      exact hy1)
  refine ⟨⟨hyunit.unit, (Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_iff
    hyunit.unit).mpr hsubmem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [powMonoidHom_apply, Subgroup.coe_pow, Subtype.coe_mk, Units.val_pow_eq_pow_val,
    IsUnit.unit_spec]
  exact Subtype.ext (by simpa using hyp)

theorem KQ_pow_range_eq_ker (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) :
    (powMonoidHom p : KQ v →* KQ v).range = (thetaHom v).ker := by
  have hvalpN : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℕ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    rw [show ((p:ℕ) : v.adicCompletion ℚ) = ((p:ℚ) : v.adicCompletion ℚ) by push_cast; rfl]
    exact hvalp
  exact le_antisymm (KQ_pow_range_le_ker v p hp hvalpN) (theta_ker_le_KQ_pow v p hp hodd hvalp)

/-! ## Cardinality of the relevant quotients -/

theorem gcd_prime_self_sub_one {p : ℕ} (hp : p.Prime) : Nat.gcd p (p - 1) = 1 := by
  have h1 : Nat.gcd p (p - 1) ∣ p := Nat.gcd_dvd_left p (p - 1)
  have h2 : Nat.gcd p (p - 1) ∣ p - 1 := Nat.gcd_dvd_right p (p - 1)
  have h3 : Nat.gcd p (p - 1) ∣ p - (p - 1) := Nat.dvd_sub h1 h2
  have h4 : p - (p - 1) = 1 := by have := hp.one_le; omega
  rw [h4] at h3
  exact Nat.dvd_one.mp h3

theorem ofAdd_pow_eq (m : ℤ) (p : ℕ) :
    (Multiplicative.ofAdd m) ^ p = Multiplicative.ofAdd ((p:ℤ) * m) := by
  rw [← ofAdd_nsmul, nsmul_eq_mul]

theorem ofAdd_zpow_eq (m k : ℤ) :
    (Multiplicative.ofAdd m) ^ k = Multiplicative.ofAdd (k * m) := by
  rw [← ofAdd_zsmul]
  congr 1

theorem natCard_multiplicative_int_quot_pow (p : ℕ) :
    Nat.card (Multiplicative ℤ ⧸ (powMonoidHom p : Multiplicative ℤ →* Multiplicative ℤ).range)
      = p := by
  have hrange : (powMonoidHom p : Multiplicative ℤ →* Multiplicative ℤ).range
      = Subgroup.zpowers (Multiplicative.ofAdd (p:ℤ)) := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨m, rfl⟩
      rw [powMonoidHom_apply]
      refine ⟨Multiplicative.toAdd m, ?_⟩
      rw [ofAdd_zpow_eq]
      conv_rhs => rw [← ofAdd_toAdd m]
      rw [ofAdd_pow_eq]
      congr 1; ring
    · rintro ⟨k, rfl⟩
      refine ⟨Multiplicative.ofAdd k, ?_⟩
      rw [powMonoidHom_apply, ofAdd_pow_eq, ofAdd_zpow_eq]
      congr 1; ring
  rw [hrange, ← Subgroup.index_eq_card, Commons.GroupTheory.Subgroup.index_zpowers_ofAdd]
  exact Int.natAbs_natCast p

theorem natCard_residue_units_quot_pow
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime)
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card ((IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ ⧸
      (powMonoidHom p).range) = 1 := by
  haveI hfin : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion ℚ v
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := Fintype.ofFinite _
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ :=
    Finite.of_injective (Units.val : (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ → IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) Units.val_injective
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ := Fintype.ofFinite _
  rw [Commons.GroupTheory.SpecificGroups.Cyclic.card_quotient_powMonoidHom
    (G := (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ) p,
    ← Nat.card_eq_fintype_card, Nat.card_units, hres]
  exact gcd_prime_self_sub_one hp

theorem natCard_KQ_quot_pow
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card (KQ v ⧸ (powMonoidHom p : KQ v →* KQ v).range) = p := by
  rw [KQ_pow_range_eq_ker v p hp hodd hvalp]
  haveI hfin : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion ℚ v
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := Fintype.ofFinite _
  have h := QuotientGroup.quotientKerEquivOfSurjective (thetaHom v) (thetaHom_surjective v)
  rw [Nat.card_congr h.toEquiv, ← Nat.card_congr (Multiplicative.ofAdd (α := IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)))]
  exact hres

theorem natCard_adicCompletionIntegers_units_quot_pow
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card ((v.adicCompletionIntegers ℚ)ˣ ⧸ (powMonoidHom p).range) = p := by
  haveI hfin : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion ℚ v
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := Fintype.ofFinite _
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ :=
    Finite.of_injective (Units.val : (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ → IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) Units.val_injective
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ := Fintype.ofFinite _
  have htor : ∀ h : (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ, h ^ p = 1 → h = 1 := by
    intro h hh
    have h1 : orderOf h ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hh
    have h2 : orderOf h ∣ p - 1 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have hc : Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))ˣ = p - 1 := by
        rw [← Nat.card_eq_fintype_card, Nat.card_units, hres]
      rw [← hc]
      exact pow_card_eq_one
    have h3 : orderOf h ∣ Nat.gcd p (p - 1) := Nat.dvd_gcd h1 h2
    rw [gcd_prime_self_sub_one hp] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have htot := natCard_quot_powMonoidHom_eq_mul
    (Units.map ((IsLocalRing.residue (v.adicCompletionIntegers ℚ)).toMonoidHom))
    (Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion v)
    p htor
  rw [htot, natCard_residue_units_quot_pow v p hp hres,
    natCard_KQ_quot_pow v p hp hodd hvalp hres, one_mul]

theorem natCard_ker_unitsValLog_quot_pow
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card ((unitsValLog (v.adicCompletion ℚ)).ker ⧸
      (powMonoidHom p : (unitsValLog (v.adicCompletion ℚ)).ker →*
        (unitsValLog (v.adicCompletion ℚ)).ker).range) = p := by
  have hA := natCard_adicCompletionIntegers_units_quot_pow v p hp hodd hvalp hres
  have hker : (unitsValLog (v.adicCompletion ℚ)).ker = (v.adicCompletionIntegers ℚ).unitGroup :=
    Commons.NumberTheory.NumberField.Completion.adicUnitsVal_eq_unitGroup ℚ v
  rw [hker]
  have he : ((powMonoidHom p : (v.adicCompletionIntegers ℚ).unitGroup →*
        (v.adicCompletionIntegers ℚ).unitGroup).range).map
        (ValuationSubring.unitGroupMulEquiv (v.adicCompletionIntegers ℚ))
      = (powMonoidHom p : (v.adicCompletionIntegers ℚ)ˣ →* (v.adicCompletionIntegers ℚ)ˣ).range := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨k, hk, hkx⟩ := hx
      rw [MonoidHom.mem_range] at hk
      obtain ⟨g, hg⟩ := hk
      have hgk : g ^ p = k := by simpa [powMonoidHom_apply] using hg
      rw [MonoidHom.mem_range]
      refine ⟨ValuationSubring.unitGroupMulEquiv _ g, ?_⟩
      rw [powMonoidHom_apply, ← map_pow, hgk]
      exact hkx
    · intro hx
      rw [MonoidHom.mem_range] at hx
      obtain ⟨k, hk⟩ := hx
      rw [Subgroup.mem_map]
      refine ⟨(ValuationSubring.unitGroupMulEquiv (v.adicCompletionIntegers ℚ)).symm (k ^ p), ?_, ?_⟩
      · rw [MonoidHom.mem_range]
        exact ⟨(ValuationSubring.unitGroupMulEquiv (v.adicCompletionIntegers ℚ)).symm k,
          by simp only [powMonoidHom_apply]; rw [← map_pow]⟩
      · rw [← hk, powMonoidHom_apply]
        exact MulEquiv.apply_symm_apply _ _
  have hidx : ((powMonoidHom p : (v.adicCompletionIntegers ℚ).unitGroup →*
        (v.adicCompletionIntegers ℚ).unitGroup).range).index
      = ((powMonoidHom p : (v.adicCompletionIntegers ℚ)ˣ →*
        (v.adicCompletionIntegers ℚ)ˣ).range).index := by
    rw [← he, Subgroup.index_map_equiv]
  calc Nat.card ((v.adicCompletionIntegers ℚ).unitGroup ⧸
        (powMonoidHom p : (v.adicCompletionIntegers ℚ).unitGroup →*
          (v.adicCompletionIntegers ℚ).unitGroup).range)
      = ((powMonoidHom p : (v.adicCompletionIntegers ℚ).unitGroup →*
          (v.adicCompletionIntegers ℚ).unitGroup).range).index := rfl
    _ = ((powMonoidHom p : (v.adicCompletionIntegers ℚ)ˣ →*
          (v.adicCompletionIntegers ℚ)ˣ).range).index := hidx
    _ = Nat.card ((v.adicCompletionIntegers ℚ)ˣ ⧸
          (powMonoidHom p : (v.adicCompletionIntegers ℚ)ˣ →*
            (v.adicCompletionIntegers ℚ)ˣ).range) := rfl
    _ = p := hA

theorem natCard_adicCompletion_units_rat_quot_pow
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2)
    (hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card ((v.adicCompletion ℚ)ˣ ⧸ (powMonoidHom p).range) = p ^ 2 := by
  have htor : ∀ h : Multiplicative ℤ, h ^ p = 1 → h = 1 := by
    intro h hh
    have h2 : Multiplicative.ofAdd ((p:ℤ) * Multiplicative.toAdd h) = 1 := by
      rw [← ofAdd_pow_eq (Multiplicative.toAdd h) p, ← ofAdd_toAdd h]
      exact hh
    have h3 : (p:ℤ) * Multiplicative.toAdd h = 0 := ofAdd_eq_one.mp h2
    have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hm : Multiplicative.toAdd h = 0 := by
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hp0
      · exact h4
    rw [← ofAdd_toAdd h, hm, ofAdd_zero]
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have htot := natCard_quot_powMonoidHom_eq_mul (unitsValLog (v.adicCompletion ℚ))
    (Commons.NumberTheory.NumberField.Completion.unitsValLog_adicCompletion_surjective ℚ v) p htor
  rw [htot, natCard_multiplicative_int_quot_pow p,
    natCard_ker_unitsValLog_quot_pow v p hp hodd hvalp hres]
  ring

/-! ## The main theorem -/

theorem natCard_powerQuotient_adicCompletion_rat_units {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hres : Nat.card (IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)) = p) :
    Nat.card ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ ⧸
      (powMonoidHom p).range) = p ^ 2 := by
  have hgen : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := by
    rw [← Commons.NumberTheory.NumberField.Set.absNorm_eq_primesEquiv v,
      ← Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm v]
    exact hres
  have hmem : (p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal :=
    Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq v p hp (Subtype.ext hgen)
  have hvalp : Valued.v (R := v.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p:ℚ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) :=
    Commons.NumberTheory.NumberField.Completion.val_prime_adicCompletion_rat hp v hmem
  exact natCard_adicCompletion_units_rat_quot_pow v p hp hodd hvalp hres

end
end Commons.NumberTheory.NumberField.Completion

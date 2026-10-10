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
import Submission.Commons.FieldTheory.Galois.div_mem_range_norm_of_prime_quotient_coprime
import Submission.Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.kernel_condition_of_prime_top_cyclic_middle_coprime
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_pgroup_intermediate_field
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The abelian local norm index theorem for `p`-groups: the base-change step

Target of this file (the requested lemma):
`Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_abelian_pgroup_base`:
for `B ⊆ E` a finite abelian Galois extension of local fields with `B` a finite extension of the
completion `Q.adicCompletion K` of a number field at a finite place, and `Gal(E/B)` a `p`-group,

`#(Bˣ ⧸ N_{E/B}(Eˣ)) = #Gal(E/B)`.

Since `IsPGroup 0 G` holds for every group `G`, the statement with `p = 0` is the *full* abelian
case, so the hypothesis `hp` is not restrictive.

## Structure of the proof

With `hupper` and `hlower` the two inequalities, the result is `le_antisymm hupper hlower`:

* `hupper` is `natCard_quotient_units_range_norm_le_card_of_abelian_local_base` (commons, PROVEN):
  `#(Bˣ ⧸ N) ≤ #Gal(E/B)` for every *abelian* `E/B`.  It is obtained by peeling off a subgroup
  `H ≤ G` with `G/H` cyclic and using the cyclic case plus the elementary tower inequality.
* `hlower` (`[E:B] ≤ #(Bˣ ⧸ N)`) is the local norm index theorem for the *lower* direction.

The lower bound is obtained from the commons lemma
`Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_pgroup_intermediate_field`
(PROVEN, by a companion agent): for `B ⊆ E` a finite abelian Galois extension of local fields over
`Q.adicCompletion K` and *every* intermediate field `M` whose extension `M/B` has `p`-group
Galois group,

`#(Bˣ ⧸ N_{M/B}(Mˣ)) = #Gal(M/B)`.

Applying it at `M = ⊤` and transporting both sides along `⊤ ≃ₐ[B] E`
(`IntermediateField.topEquiv`, via `natCard_quotient_units_range_norm_eq_of_ringEquiv` and
`AlgEquiv.autCongr`) gives exactly the lower bound for the extension `E/B`; the `p`-group
hypothesis transports because `AlgEquiv.autCongr (topEquiv)` is an isomorphism of groups.  Since
`IsPGroup 0 G` holds for every group `G`, the statement with `p = 0` is the *full* abelian case, so
the hypothesis `hp` is not restrictive.

## The lower bound: what is used and what is proven in this file

The lower bound is the deep local class field theory input; it is proved in the companion commons
file cited above (via the fundamental class / Tate's theorem route), and it is not reproved here.
Everything in this file serves the valuation-theoretic analysis of the norm index and the transport
of the extension data:

* (`NormIndexUnits.natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux`)
  the **valuation formula**: the value-group logarithm `unitsValLog B` (commons) is surjective with
  kernel `U = (Q.adicCompletionIntegers K).unitGroup` and satisfies
  `unitsValLog (N u) = (unitsValLog u)^f` for `u ∈ Eˣ`, where `f` is the inertia degree of `q | Q`;
  hence `v(N Eˣ) = fℤ` and

  `#(Bˣ ⧸ N) = f · [U : U ∩ N]`.

* (`NormIndexUnits.finrank_le_index_range_norm_adicCompletion_of_units`)
  consequently it **suffices** to know `[U : U ∩ N] = e` (`e` = ramification index), i.e.

  `(range N).relIndex U = q.asIdeal.ramificationIdx (𝓞 K)`.

* (`inertiaDeg_le_natCard_quotient_units_range_norm_adicCompletion`) the special case
  `[U : U ∩ N] ≥ 1` of that statement gives `#(Bˣ ⧸ N) ≥ f`, i.e. the norm index theorem for
  unramified `E/B`.

* (`exists_norm_units_of_unramified_top_and_dvd_ramificationIdx`) the arithmetic content of the
  residual case of Milne's divisibility step (Milne, *CFT*, III.2) for the unramified twist.

* (`isGalois_of_ringEquiv`, `norm_eq_of_ringEquiv`, `moduleFinite_of_ringEquiv`,
  `natCard_quotient_units_range_norm_eq_of_ringEquiv`) the transport of the field-theoretic data
  (Galois-ness, the norm, finite-dimensionality, the norm quotient) along a compatible pair of ring
  isomorphisms — the algebraic half of the universe bridge.

Further context: the upper bound (`natCard_quotient_units_range_norm_le_card_of_abelian_local_base`),
the cyclic case (`natCard_quotient_units_range_norm_eq_card_of_cyclic*`), the unramified case
(`..._of_ramificationIdx_eq_one`), the kernel condition for an unramified or cyclic middle
(`kernel_condition_of_unramified_top`, `kernel_condition_of_prime_top_cyclic_middle_coprime`),
and Hilbert 90 are all in the commons.
-/

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum

/-! ## The valuation formula: the norm index splits as `f` times the unit part

Writing `v` for the value-group logarithm `unitsValLog` of `B = Q.adicCompletion K` and
`U = v.ker = (Q.adicCompletionIntegers K).unitGroup`, the identity `v (N u) = (v u)^f`
(`unitsValLog_norm`, `f` = inertia degree) shows that the norm group has value group `fℤ`, so
the index of the norm group splits as `f` times the index of `U ∩ N_{E/B}(Eˣ)` in `U`.
-/

namespace NormIndexUnits

lemma toAdd_pow_multiplicative (a : Multiplicative ℤ) (n : ℕ) :
    (a ^ n).toAdd = (n : ℤ) * a.toAdd := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, show (a ^ k * a).toAdd = (a ^ k).toAdd + a.toAdd from rfl, ih]
      push_cast
      ring

lemma ofAdd_pow (a : ℤ) (n : ℕ) :
    (Multiplicative.ofAdd a) ^ n = Multiplicative.ofAdd ((n : ℤ) * a) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow_multiplicative]
  rfl

noncomputable def multIntToZMod (n : ℕ) : Multiplicative ℤ →* Multiplicative (ZMod n) :=
  AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))

lemma multIntToZMod_apply (n : ℕ) (z : Multiplicative ℤ) :
    multIntToZMod n z = Multiplicative.ofAdd ((z.toAdd : ℤ) : ZMod n) := rfl

lemma multIntToZMod_ofAdd_pow_self (n : ℕ) (a : ℤ) :
    multIntToZMod n ((Multiplicative.ofAdd a) ^ n) = 1 := by
  have hzero : (((n : ℤ)) : ZMod n) = 0 := by rw [Int.cast_natCast, ZMod.natCast_self]
  rw [ofAdd_pow, multIntToZMod_apply]
  change Multiplicative.ofAdd ((((n : ℤ) * a : ℤ)) : ZMod n) = 1
  rw [Int.cast_mul, hzero, zero_mul]
  rfl

lemma multIntToZMod_surjective (n : ℕ) : Function.Surjective (multIntToZMod n) := by
  intro y
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (b := y.toAdd)
  refine ⟨Multiplicative.ofAdd z, ?_⟩
  rw [multIntToZMod_apply]
  exact congrArg Multiplicative.ofAdd hz

lemma multIntToZMod_eq_one_iff (n : ℕ) (z : Multiplicative ℤ) :
    multIntToZMod n z = 1 ↔ (n : ℤ) ∣ z.toAdd := by
  rw [multIntToZMod_apply, ← ZMod.intCast_zmod_eq_zero_iff_dvd (a := z.toAdd) (b := n)]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    simpa using h'
  · intro h
    rw [h]
    rfl

end NormIndexUnits

namespace NormIndexUnits

/-- **The valuation formula for the norm index.**  The index of the norm group splits as the
inertia degree times the index of the unit part. -/
theorem natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K))) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) *
        (MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K))).relIndex (adicUnitsVal K Q) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  set f := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) with hf
  set B := (Q.adicCompletion K)ˣ with hB
  set U : Subgroup B := adicUnitsVal K Q with hU
  set N : Subgroup B := MonoidHom.range
    (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)) with hN
  set w : B →* Multiplicative (ZMod f) :=
    (multIntToZMod f).comp (unitsValLog (Q.adicCompletion K)) with hw
  have hw_apply : ∀ x : B, w x = multIntToZMod f (unitsValLog (Q.adicCompletion K) x) := fun x => rfl
  have hUker : U = (unitsValLog (Q.adicCompletion K)).ker := rfl
  have hNle : N ≤ w.ker := by
    rintro x ⟨u, rfl⟩
    rw [MonoidHom.mem_ker, hw_apply, unitsValLog_norm Q q hq u,
      unitsValLog_apply (q.adicCompletion L)]
    exact multIntToZMod_ofAdd_pow_self f _
  -- `w.ker = U ⊔ N`
  have hwk : U ⊔ N = w.ker := by
    refine le_antisymm (sup_le ?_ hNle) ?_
    · intro x hx
      rw [MonoidHom.mem_ker, hw_apply, show unitsValLog (Q.adicCompletion K) x = 1 from
        MonoidHom.mem_ker.mp hx, map_one]
    · intro x hx
      rw [MonoidHom.mem_ker, hw_apply, multIntToZMod_eq_one_iff] at hx
      obtain ⟨m, hm⟩ := hx
      obtain ⟨u, hu⟩ := unitsValLog_adicCompletion_surjective L q (Multiplicative.ofAdd m)
      set z : B := Units.map (Algebra.norm (Q.adicCompletion K) :
        q.adicCompletion L →* Q.adicCompletion K) u with hz
      have hzval : unitsValLog (Q.adicCompletion K) z = unitsValLog (Q.adicCompletion K) x := by
        apply Multiplicative.toAdd.injective
        rw [hz, unitsValLog_norm Q q hq u, hu, toAdd_pow_multiplicative, hm, ← hf]
        rfl
      have hmem : x * z⁻¹ ∈ U := by
        rw [hUker, MonoidHom.mem_ker, map_mul, map_inv, hzval, mul_inv_cancel]
      refine Subgroup.mem_sup.mpr ⟨x * z⁻¹, hmem, z, ⟨u, hz⟩, ?_⟩
      simp
  have hcard : (U ⊔ N).index = f := by
    rw [hwk, Subgroup.index_ker]
    have hrange : w.range = ⊤ := MonoidHom.range_eq_top.mpr
      ((multIntToZMod_surjective f).comp (unitsValLog_adicCompletion_surjective K Q))
    rw [hrange, Subgroup.card_top]
    exact Nat.card_zmod f
  haveI : N.Normal := Subgroup.normal_of_isMulCommutative N
  calc Nat.card (B ⧸ N) = N.index := Subgroup.index_eq_card N
    _ = N.relIndex (U ⊔ N) * (U ⊔ N).index :=
        (Subgroup.relIndex_mul_index (le_sup_right : N ≤ U ⊔ N)).symm
    _ = N.relIndex U * (U ⊔ N).index := by rw [Subgroup.relIndex_sup_right (H := U)]
    _ = N.relIndex U * f := by rw [hcard]
    _ = f * N.relIndex U := by rw [mul_comm]


/-- **Reduction of the lower bound to the unit statement** (Herbrand's theorem).

If the unit part `[U : U ∩ N_{E/B}(Eˣ)]` of the norm index equals the ramification index `e`, then
the full norm index is the degree `[E : B] = e·f`: combine the valuation formula with
`finrank = e·f`.  This isolates the class-field-theoretic input as a statement about the unit
groups only. -/
theorem finrank_le_index_range_norm_adicCompletion_of_units
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    (MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
        q.adicCompletion L →* Q.adicCompletion K))).relIndex (adicUnitsVal K Q) =
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) →
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) ≤
        (MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K))).index := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro hun
  have hval := natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux Q q hq
  rw [Subgroup.index_eq_card, hval, hun]
  rw [← Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq]
  exact le_of_eq (Nat.mul_comm _ _)

end NormIndexUnits


/-! ## The "inertia degree" half of the lower bound

The value-group logarithm `unitsValLog (Q.adicCompletion K) : (Q.adicCompletion K)ˣ →* Multiplicative ℤ`
is surjective with kernel the unit group of the valuation ring, and
`unitsValLog (N u) = (unitsValLog u) ^ f` where `f` is the inertia degree of `q | Q`.  Hence the
norm group is contained in the preimage of `fℤ`, giving the lower bound `f ≤ #(Bˣ ⧸ N)`.  -/

open NormIndexUnits

/-- **The norm index is at least the inertia degree.**  For `L/K` a finite Galois extension of
number fields and `q | Q` a place, with `B = Q.adicCompletion K` and `E = q.adicCompletion L`, the
index of the norm group `N_{E/B}(Eˣ)` in `Bˣ` is at least the inertia degree of `q` over `Q`. -/
theorem inertiaDeg_le_natCard_quotient_units_range_norm_adicCompletion
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≤
      Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K))) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  set f := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) with hf
  set B := (Q.adicCompletion K)ˣ with hB
  set N : Subgroup B := MonoidHom.range
    (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)) with hN
  set w : B →* Multiplicative (ZMod f) :=
    (multIntToZMod f).comp (unitsValLog (Q.adicCompletion K)) with hw
  have hw_apply : ∀ x : B, w x = multIntToZMod f (unitsValLog (Q.adicCompletion K) x) := fun x => rfl
  have hNle : N ≤ w.ker := by
    rintro x ⟨u, rfl⟩
    rw [MonoidHom.mem_ker, hw_apply, unitsValLog_norm Q q hq u,
      unitsValLog_apply (q.adicCompletion L)]
    exact multIntToZMod_ofAdd_pow_self f _
  have hwsurj : Function.Surjective w :=
    (multIntToZMod_surjective f).comp (unitsValLog_adicCompletion_surjective K Q)
  haveI hNnormal : N.Normal := Subgroup.normal_of_isMulCommutative N
  haveI hKnormal : w.ker.Normal := MonoidHom.normal_ker w
  have hsurj : Function.Surjective
      (QuotientGroup.lift N (QuotientGroup.mk' w.ker) (by
        rw [QuotientGroup.ker_mk']
        exact hNle)) := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective w.ker y
    refine ⟨QuotientGroup.mk x, ?_⟩
    rw [← hx, QuotientGroup.lift_mk']
  have hcard : Nat.card (B ⧸ w.ker) = f := by
    rw [(Subgroup.index_eq_card w.ker).symm, Subgroup.index_ker]
    have hrange : w.range = ⊤ := MonoidHom.range_eq_top.mpr hwsurj
    rw [hrange, Subgroup.card_top]
    exact Nat.card_zmod f
  haveI : Finite (B ⧸ N) :=
    finite_quotient_units_range_norm_adicCompletion (K := K) (L := L) Q q hq
  calc f = Nat.card (B ⧸ w.ker) := hcard.symm
    _ ≤ Nat.card (B ⧸ N) := Nat.card_le_card_of_surjective _ hsurj

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

namespace PrimeTopFracture

/-- **Fracture step**: the prime-top kernel condition follows from its unit form.
Pure valuation theory: if `N_{B/F}(x) = 1` then `v_B(x)^f = v_F(1) = 1`, so `x` is a unit of `B`,
and the unit statement applies. -/
theorem kernel_condition_of_prime_top_adicCompletion_of_units
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂] [IsGalois L₀ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hq₀₂ : q₂.asIdeal.LiesOver q₀.asIdeal) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    (∀ u : adicUnitsVal L₁ q₁,
        Algebra.norm (q₀.adicCompletion L₀) ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) = 1 →
        ∃ w : (q₂.adicCompletion L₂)ˣ,
          Algebra.norm (q₁.adicCompletion L₁) (w : q₂.adicCompletion L₂) =
            ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁)) →
      MonoidHom.ker (Units.map (Algebra.norm (q₀.adicCompletion L₀) :
          q₁.adicCompletion L₁ →* q₀.adicCompletion L₀)) ≤
        MonoidHom.range (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
          q₂.adicCompletion L₂ →* q₁.adicCompletion L₁)) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  intro hunit x hx
  rw [MonoidHom.mem_ker] at hx
  set f := q₁.asIdeal.inertiaDeg (NumberField.RingOfIntegers L₀) with hf
  have hfne : f ≠ 0 := (Ideal.inertiaDeg_pos (q := q₁.asIdeal)
    (R := NumberField.RingOfIntegers L₀)).ne'
  -- `x` is a unit of `q₁.adicCompletion L₁`
  have hxU : x ∈ adicUnitsVal L₁ q₁ := by
    have hkey := unitsValLog_norm q₀ q₁ hq₁ x
    rw [hx, map_one] at hkey
    have hpow : (unitsValLog (q₁.adicCompletion L₁) x) ^ f = (1 : Multiplicative ℤ) ^ f := by
      rw [← hkey, one_pow]
    have h1 : unitsValLog (q₁.adicCompletion L₁) x = 1 :=
      pow_right_injective_zint hfne hpow
    simpa [adicUnitsVal, MonoidHom.mem_ker] using h1
  have hxval : Algebra.norm (q₀.adicCompletion L₀) ((x : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) = 1 := by
    have h := congrArg (fun u : (q₀.adicCompletion L₀)ˣ => (u : q₀.adicCompletion L₀)) hx
    simpa using h
  obtain ⟨w, hw⟩ := hunit ⟨x, hxU⟩ hxval
  exact ⟨w, Units.ext hw⟩

end PrimeTopFracture

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false

theorem exists_algEquiv_lift {F B E : Type*} [Field F] [Field B] [Field E]
    [Algebra F B] [Algebra F E] [Algebra B E] [IsScalarTower F B E]
    [FiniteDimensional F B] [FiniteDimensional F E] [FiniteDimensional B E]
    [IsGalois F B] [IsGalois F E] [IsGalois B E]
    (σ : B ≃ₐ[F] B) :
    ∃ τ : E ≃ₐ[F] E, ∀ x : B, τ (algebraMap B E x) = algebraMap B E (σ x) := by
  let hBE : B →ₐ[F] E := IsScalarTower.toAlgHom F B E
  let K : IntermediateField F E := hBE.fieldRange
  let i : B ≃ₐ[F] ↥K := AlgEquiv.ofInjectiveField hBE
  haveI hKgal : IsGalois F ↥K := IsGalois.of_algEquiv i
  haveI hKnormal : Normal F ↥K := hKgal.to_normal
  let σK : ↥K ≃ₐ[F] ↥K := i.symm.trans (σ.trans i)
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥K) (E := E) σK
  refine ⟨τ, ?_⟩
  intro x
  have hx : (i x : E) = algebraMap B E x := rfl
  have h2 : ((AlgEquiv.restrictNormalHom ↥K τ) (i x) : E) = (σK (i x) : E) := by
    rw [hτ]
  have h3 : τ ((i x : E)) = ((AlgEquiv.restrictNormalHom ↥K τ) (i x) : E) :=
    (AlgEquiv.restrictNormalHom_apply K τ (i x)).symm
  have h4 : (σK (i x) : E) = algebraMap B E (σ x) := by
    show ((i.symm.trans (σ.trans i)) (i x) : E) = _
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply]
    have : i.symm (i x) = x := i.symm_apply_apply x
    rw [this]
    rfl
  rw [← hx, h3, h2, h4]

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

/-! ## The `Y`-action on the norm group (the `I_Y`-coprimality step of the fracture)

The norm group `N_{E/B}(Eˣ)` is stable under any automorphism of `B` that lifts to `E`:
for compatible `σ : B ≃ₐ[F] B`, `τ : E ≃ₐ[F] E` one has `σ (N_{E/B} x) = N_{E/B} (τ x)`
(`Algebra.norm_eq_of_equiv_equiv`).  This is what makes the `Gal(B/F)`-action on the
quotient `Bˣ ⧸ N_{E/B}(Eˣ)` (and on `U_B ⧸ (U_B ∩ N_{E/B}(Eˣ))`) well defined.
-/

theorem map_norm_eq_of_apply_eq {F B E : Type*} [Field F] [Field B] [Field E]
    [Algebra F B] [Algebra F E] [Algebra B E] [IsScalarTower F B E]
    (σ : B ≃ₐ[F] B) (τ : E ≃ₐ[F] E)
    (h : ∀ x : B, τ (algebraMap B E x) = algebraMap B E (σ x)) (x : E) :
    σ (Algebra.norm B x) = Algebra.norm B (τ x) := by
  have he : RingHom.comp (algebraMap B E) ↑σ.toRingEquiv =
      RingHom.comp ↑τ.toRingEquiv (algebraMap B E) := by
    ext y
    exact (h y).symm
  have key := Algebra.norm_eq_of_equiv_equiv σ.toRingEquiv τ.toRingEquiv he x
  rw [key]
  exact RingEquiv.apply_symm_apply σ.toRingEquiv (Algebra.norm B (τ.toRingEquiv x))

/-- The norm group of units is stable under any automorphism of the base that lifts. -/
theorem map_range_norm_units_le_of_apply_eq {F B E : Type*} [Field F] [Field B] [Field E]
    [Algebra F B] [Algebra F E] [Algebra B E] [IsScalarTower F B E]
    (σ : B ≃ₐ[F] B) (τ : E ≃ₐ[F] E)
    (h : ∀ x : B, τ (algebraMap B E x) = algebraMap B E (σ x)) :
    (MonoidHom.range (Units.map (Algebra.norm B : E →* B))).map
        (Units.map σ.toRingEquiv.toMonoidHom) ≤
      MonoidHom.range (Units.map (Algebra.norm B : E →* B)) := by
  rintro y ⟨u, hu, rfl⟩
  obtain ⟨w, rfl⟩ := hu
  refine ⟨Units.map τ.toRingEquiv.toMonoidHom w, ?_⟩
  ext
  simp only [Units.coe_map]
  exact (map_norm_eq_of_apply_eq σ τ h (w : E)).symm

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- **The `I_Y`-coprimality step.**  In the prime-top situation (`[E : B₁] = p` prime, `E/B`
abelian not needed here, but `#Gal(B₁/B)` coprime to `p - 1`), every `σ ∈ Gal(B₁/B)` acts trivially
on `B₁ˣ ⧸ N_{E/B₁}(Eˣ)`: for all `u`, `σ u / u ∈ N_{E/B₁}(Eˣ)`. -/
theorem augmentation_adicUnitsVal_le_range_norm_of_prime_top
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂] [IsGalois L₀ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hq₀₂ : q₂.asIdeal.LiesOver q₀.asIdeal) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    Nat.Prime (Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂)) →
    (Nat.card (q₁.adicCompletion L₁ ≃ₐ[q₀.adicCompletion L₀] q₁.adicCompletion L₁)).Coprime
        (Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) - 1) →
    ∀ (σ : q₁.adicCompletion L₁ ≃ₐ[q₀.adicCompletion L₀] q₁.adicCompletion L₁)
      (u : adicUnitsVal L₁ q₁),
      Units.map σ.toRingEquiv.toMonoidHom u / u ∈
        MonoidHom.range (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
          q₂.adicCompletion L₂ →* q₁.adicCompletion L₁)) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  intro hprime hcop σ u
  haveI hst : IsScalarTower (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    simpa [RingHom.comp_apply] using (RingHom.congr_fun
      (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp q₀ q₁ q₂ hq₁ hq₂ hq₀₂) x).symm
  haveI : FiniteDimensional (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    module_finite_adicCompletion q₀ q₁ hq₁
  haveI : FiniteDimensional (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    module_finite_adicCompletion q₀ q₂ hq₀₂
  haveI : IsGalois (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    isGalois_adicCompletion q₀ q₁ hq₁
  haveI : IsGalois (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    isGalois_adicCompletion q₀ q₂ hq₀₂
  haveI : IsGalois (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    isGalois_adicCompletion q₁ q₂ hq₂
  haveI : FiniteDimensional (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    module_finite_adicCompletion q₁ q₂ hq₂
  have hcard : Nat.card (q₂.adicCompletion L₂ ≃ₐ[q₁.adicCompletion L₁] q₂.adicCompletion L₂) =
      Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    IsGalois.card_aut_eq_finrank _ _
  haveI : Fact (Nat.Prime (Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂))) :=
    ⟨hprime⟩
  haveI : IsCyclic (q₂.adicCompletion L₂ ≃ₐ[q₁.adicCompletion L₁] q₂.adicCompletion L₂) :=
    isCyclic_of_prime_card hcard
  have hnorm : Nat.card ((q₁.adicCompletion L₁)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
          q₂.adicCompletion L₂ →* q₁.adicCompletion L₁))) =
      Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) := by
    rw [natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base' (K := L₀) (Q := q₀)
      (B := q₁.adicCompletion L₁) (B₁ := q₂.adicCompletion L₂), hcard]
  exact Commons.FieldTheory.Galois.div_mem_range_norm_of_prime_quotient_coprime
    (B := q₀.adicCompletion L₀) (B₁ := q₁.adicCompletion L₁) (E := q₂.adicCompletion L₂)
    (by rw [hnorm]; exact hprime) (by rw [hnorm]; exact hcop) σ u

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- **The unramified case of the unit-level prime-top statement.**  If the top step `E/B` is
unramified, every unit of `B` is a norm from `E` (the norm is surjective on units), so the
`H₂`-torsor statement holds for all `u`. -/
theorem forall_ker_adicUnitsVal_le_range_norm_of_ramificationIdx_eq_one
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂] [IsGalois L₀ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hq₀₂ : q₂.asIdeal.LiesOver q₀.asIdeal)
    (hunr : q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁) = 1) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    ∀ u : adicUnitsVal L₁ q₁,
      ∃ w : (q₂.adicCompletion L₂)ˣ,
        Algebra.norm (q₁.adicCompletion L₁) (w : q₂.adicCompletion L₂) =
          ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  intro u
  haveI : IsGalois (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    isGalois_adicCompletion q₁ q₂ hq₂
  haveI : FiniteDimensional (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    module_finite_adicCompletion q₁ q₂ hq₂
  have hv : Valued.v (R := q₁.adicCompletion L₁) (Γ₀ := WithZero (Multiplicative ℤ))
      ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) = 1 :=
    (mem_adicUnitsVal L₁ q₁ (u : (q₁.adicCompletion L₁)ˣ)).mp u.2
  obtain ⟨x, hx⟩ := norm_units_surjective_of_ramificationIdx_eq_one q₁ q₂ hq₂ hunr
    ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) hv
  have hxu : x ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hx
    exact (Units.ne_zero (u : (q₁.adicCompletion L₁)ˣ)) hx.symm
  exact ⟨Units.mk0 x hxu, by rw [Units.val_mk0]; exact hx⟩

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

/-- **Reduction of the `H₂`-torsor statement to the totally ramified prime case.**  If the top step
`E/B` is either unramified or has ramification index equal to the (prime) degree, then the
statement holds: the ramification index divides the prime degree, so it is `1` or `p`, and the case
`e = 1` is the proven unramified case. -/
theorem ker_adicUnitsVal_le_range_norm_of_prime_top_of_ramified
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂] [IsGalois L₀ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hq₀₂ : q₂.asIdeal.LiesOver q₀.asIdeal) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    (∀ u : adicUnitsVal L₁ q₁,
      q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁) =
          Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) →
      Algebra.norm (q₀.adicCompletion L₀)
          ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) = 1 →
      ∃ w : (q₂.adicCompletion L₂)ˣ,
        Algebra.norm (q₁.adicCompletion L₁) (w : q₂.adicCompletion L₂) =
          ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁)) →
    (∀ a b : q₂.adicCompletion L₂ ≃ₐ[q₀.adicCompletion L₀] q₂.adicCompletion L₂, a * b = b * a) →
    Nat.Prime (Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂)) →
    ∀ u : adicUnitsVal L₁ q₁,
      Algebra.norm (q₀.adicCompletion L₀)
          ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) = 1 →
      ∃ w : (q₂.adicCompletion L₂)ˣ,
        Algebra.norm (q₁.adicCompletion L₁) (w : q₂.adicCompletion L₂) =
          ((u : (q₁.adicCompletion L₁)ˣ) : q₁.adicCompletion L₁) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  intro hram _hcomm hprime u hu
  -- the ramification index divides the prime degree
  have hdvd : q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁) ∣
      Module.finrank (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    ⟨q₂.asIdeal.inertiaDeg (NumberField.RingOfIntegers L₁), by
      rw [Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        q₁ q₂ hq₂]⟩
  rcases Nat.Prime.eq_one_or_self_of_dvd hprime
    (q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁)) hdvd with h1 | hp
  · -- unramified case
    obtain ⟨w, hw⟩ := forall_ker_adicUnitsVal_le_range_norm_of_ramificationIdx_eq_one
      q₀ q₁ q₂ hq₁ hq₂ hq₀₂ h1 u
    exact ⟨w, hw⟩
  · -- totally ramified prime case: the hypothesis
    exact hram u hp hu

end Commons.NumberTheory.NumberField.Completion

namespace Commons.NumberTheory.NumberField.Completion

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- **Node 1 of the totally ramified plan: the unit part of the norm group.**

A *unit* of `B` is a norm from `E` if and only if it is the norm of a *unit* of `E`:
`U_B ⊓ N_{E/B}(Eˣ) = N_{E/B}(U_E)` as subgroups of `Bˣ`.

Both inclusions are the valuation identity `v_B(N x) = f · v_E(x)` (`unitsValLog_norm` at the pair
`(q₁, q₂)`) together with `f ≠ 0`. -/
theorem inf_adicUnitsVal_range_norm_units_eq_map_adicUnitsVal
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂] [IsGalois L₀ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hq₀₂ : q₂.asIdeal.LiesOver q₀.asIdeal) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    adicUnitsVal L₁ q₁ ⊓ MonoidHom.range (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
        q₂.adicCompletion L₂ →* q₁.adicCompletion L₁)) =
      Subgroup.map (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
          q₂.adicCompletion L₂ →* q₁.adicCompletion L₁)) (adicUnitsVal L₂ q₂) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₀.adicCompletion L₀) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₂ hq₀₂)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  haveI : IsGalois (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    isGalois_adicCompletion q₁ q₂ hq₂
  haveI : FiniteDimensional (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    module_finite_adicCompletion q₁ q₂ hq₂
  set f := q₂.asIdeal.inertiaDeg (NumberField.RingOfIntegers L₁) with hf
  have hfne : f ≠ 0 := (Ideal.inertiaDeg_pos (q := q₂.asIdeal)
    (R := NumberField.RingOfIntegers L₁)).ne'
  ext y
  constructor
  · rintro ⟨hyU, x, rfl⟩
    -- `x : (q₂.adicCompletion L₂)ˣ`; show `x` is a unit of `E`
    have hkey := unitsValLog_norm q₁ q₂ hq₂ x
    have h1 : unitsValLog (q₁.adicCompletion L₁)
        (Units.map (Algebra.norm (q₁.adicCompletion L₁) :
          q₂.adicCompletion L₂ →* q₁.adicCompletion L₁) x) = 1 :=
      (unitsValLog_eq_one_iff _).mpr ((mem_adicUnitsVal L₁ q₁ _).mp hyU)
    rw [h1] at hkey
    have hx : unitsValLog (q₂.adicCompletion L₂) x = 1 :=
      pow_right_injective_zint hfne (by rw [← hkey, one_pow])
    exact ⟨x, (mem_adicUnitsVal L₂ q₂ x).mpr ((unitsValLog_eq_one_iff _).mp hx), rfl⟩
  · rintro ⟨x, hxU, rfl⟩
    refine ⟨?_, ⟨x, rfl⟩⟩
    refine (mem_adicUnitsVal L₁ q₁ _).mpr ?_
    refine (unitsValLog_eq_one_iff _).mp ?_
    rw [unitsValLog_norm q₁ q₂ hq₂ x,
      (unitsValLog_eq_one_iff _).mpr ((mem_adicUnitsVal L₂ q₂ x).mp hxU), one_pow]

end Commons.NumberTheory.NumberField.Completion

namespace Commons.FieldTheory.Galois

/-- The fixing subgroup of a binary supremum is the intersection of the fixing subgroups. -/
lemma fixingSubgroup_sup {F M : Type*} [Field F] [Field M] [Algebra F M]
    (L₁ L₂ : IntermediateField F M) :
    (L₁ ⊔ L₂).fixingSubgroup = L₁.fixingSubgroup ⊓ L₂.fixingSubgroup := by
  apply le_antisymm
  · exact le_inf (IntermediateField.fixingSubgroup_antitone le_sup_left)
      (IntermediateField.fixingSubgroup_antitone le_sup_right)
  · rw [← IntermediateField.le_iff_le (H := L₁.fixingSubgroup ⊓ L₂.fixingSubgroup)
      (K := L₁ ⊔ L₂)]
    refine sup_le ?_ ?_
    · rw [IntermediateField.le_iff_le (H := L₁.fixingSubgroup ⊓ L₂.fixingSubgroup) (K := L₁)]
      exact inf_le_left
    · rw [IntermediateField.le_iff_le (H := L₁.fixingSubgroup ⊓ L₂.fixingSubgroup) (K := L₂)]
      exact inf_le_right

/-- **The Galois group of a compositum of two independent Galois extensions.**

Let `M/F` be a finite Galois extension of fields and let `L₁ L₂ : IntermediateField F M` be
finite Galois subextensions with `L₁ ⊔ L₂ = ⊤` and `L₁ ⊓ L₂ = ⊥`.  Then the restriction maps
`Gal(M/F) → Gal(Lᵢ/F)` combine into an isomorphism `Gal(M/F) ≃* Gal(L₁/F) × Gal(L₂/F)`.

This is the standard "compositum of linearly disjoint Galois extensions" statement: the map is
injective because an automorphism fixing `L₁` and `L₂` pointwise fixes their compositum `⊤`, and
it is surjective by counting, since `[L₁ ⊔ L₂ : F] = [L₁ : F] · [L₂ : F]` when `L₁ ⊓ L₂ = ⊥`.

It is the structure theorem for the field `M = L₁·L₂` used by the unramified twist: it turns
`Gal(M/F)` into a direct product, so that inflation along the first factor followed by restriction
to the second is the coefficient map (see the roadmap note). -/
theorem galoisGroup_sup_mulEquiv_prod {F M : Type*} [Field F] [Field M] [Algebra F M]
    [FiniteDimensional F M] [IsGalois F M]
    (L₁ L₂ : IntermediateField F M) [FiniteDimensional F ↥L₁] [FiniteDimensional F ↥L₂]
    [IsGalois F ↥L₁] [IsGalois F ↥L₂]
    (hsup : L₁ ⊔ L₂ = ⊤) (hinf : L₁ ⊓ L₂ = ⊥) :
    Nonempty ((M ≃ₐ[F] M) ≃* ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂))) := by
  haveI hN₁ : Normal F ↥L₁ := inferInstance
  haveI hN₂ : Normal F ↥L₂ := inferInstance
  let φ : (M ≃ₐ[F] M) →* ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂)) :=
    MonoidHom.prod (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₁)
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₂)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ
    have h1 : (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₁) σ = 1 := by
      have h := congrArg Prod.fst hσ
      simpa [φ] using h
    have h2 : (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L₂) σ = 1 := by
      have h := congrArg Prod.snd hσ
      simpa [φ] using h
    have hmem1 : σ ∈ L₁.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have key := AlgEquiv.restrictNormalHom_apply (F := F) (K₁ := M) L₁ σ ⟨x, hx⟩
      rw [h1] at key
      simpa using key.symm
    have hmem2 : σ ∈ L₂.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have key := AlgEquiv.restrictNormalHom_apply (F := F) (K₁ := M) L₂ σ ⟨x, hx⟩
      rw [h2] at key
      simpa using key.symm
    have hbot : L₁.fixingSubgroup ⊓ L₂.fixingSubgroup = ⊥ := by
      rw [← fixingSubgroup_sup L₁ L₂, hsup]
      rw [Subgroup.eq_bot_iff_forall]
      intro τ hτ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      ext x
      exact hτ x trivial
    have hmem : σ ∈ L₁.fixingSubgroup ⊓ L₂.fixingSubgroup := ⟨hmem1, hmem2⟩
    rw [hbot] at hmem
    simpa using hmem
  refine ⟨MulEquiv.ofBijective φ ⟨hinj, ?_⟩⟩
  have hcard : Nat.card (M ≃ₐ[F] M) =
      Nat.card ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂)) := by
    rw [Nat.card_prod, IsGalois.card_aut_eq_finrank F M, IsGalois.card_aut_eq_finrank F ↥L₁,
      IsGalois.card_aut_eq_finrank F ↥L₂]
    have hd := IntermediateField.LinearDisjoint.finrank_sup
      (IntermediateField.LinearDisjoint.of_inf_eq_bot (F := F) hinf)
    rw [hsup] at hd
    rw [show Module.finrank F ↥(⊤ : IntermediateField F M) = Module.finrank F M from
      finrank_top F M] at hd
    exact hd
  haveI : Fintype ((↥L₁ ≃ₐ[F] ↥L₁) × (↥L₂ ≃ₐ[F] ↥L₂)) := Fintype.ofFinite _
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]; exact hcard⟩
  exact hbij.2

end Commons.FieldTheory.Galois

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory Representation groupCohomology Rep

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient morphism of the unramified twist: the inclusion of the `(1 × Q)`-invariants
of a representation `A` of `P × Q` into `A`, transported to a morphism of representations of `P`
along `QuotientGroup.mk' (ker fst)`. -/
noncomputable def coeffMor {k : Type u} [CommRing k] {P Q : Type u} [Group P] [Group Q]
    (A : Rep k (P × Q)) :
    (Rep.resFunctor (MonoidHom.inl P Q)).obj
        ((Rep.resFunctor (QuotientGroup.mk' (MonoidHom.ker (MonoidHom.fst P Q)))).obj
          (A.quotientToInvariants (MonoidHom.ker (MonoidHom.fst P Q)))) ⟶
      (Rep.resFunctor (MonoidHom.inl P Q)).obj A :=
  (Rep.resFunctor (MonoidHom.inl P Q)).map
      (ofHom (A.ρ.quotientToInvariants_lift (MonoidHom.ker (MonoidHom.fst P Q)))) ≫
    𝟙 (Rep.res (MonoidHom.inl P Q) A)

set_option backward.isDefEq.respectTransparency false in
/-- **The formal identity of the unramified twist** (general coefficient ring).

With `S := ker (fst : P × Q →* P) = 1 × Q` and `A` a representation of `P × Q`, the composite

`H²((P×Q) ⧸ S, A^S) --Inf_{S}--> H²(P×Q, A) --Res_{inl}--> H²(P, A)`

of the inflation along the projection onto the second factor with the restriction to the
complementary factor `P = P × 1` is the map on `H²` induced by the coefficient morphism
`coeffMor A` (the inclusion of the `S`-invariants `A^S ↪ A`), transported along the canonical
isomorphism `(QuotientGroup.mk' S).comp (MonoidHom.inl P Q) : P ≃* (P × Q) ⧸ S`.

Formally this is the functoriality `map_comp` of group cohomology; the content is the
identification of the right hand side as the *coefficient map*, i.e. that restriction to the
complementary factor inverts the inflation. -/
theorem inf_comp_res_eq_map_coeff {k : Type u} [CommRing k] {P Q : Type u} [Group P] [Group Q]
    (A : Rep k (P × Q)) :
    (groupCohomology.infNatTrans k (MonoidHom.ker (MonoidHom.fst P Q)) 2).app A ≫
      (groupCohomology.resNatTrans k (G := P) (H := P × Q) (MonoidHom.inl P Q) 2).app A
    = groupCohomology.map
        ((QuotientGroup.mk' (MonoidHom.ker (MonoidHom.fst P Q))).comp (MonoidHom.inl P Q))
        (coeffMor A) 2 := by
  have h1 : (groupCohomology.infNatTrans k (MonoidHom.ker (MonoidHom.fst P Q)) 2).app A
      = groupCohomology.map (QuotientGroup.mk' (MonoidHom.ker (MonoidHom.fst P Q)))
          (ofHom (A.ρ.quotientToInvariants_lift (MonoidHom.ker (MonoidHom.fst P Q)))) 2 := rfl
  have h2 : (groupCohomology.resNatTrans k (G := P) (H := P × Q) (MonoidHom.inl P Q) 2).app A
      = groupCohomology.map (MonoidHom.inl P Q) (𝟙 (Rep.res (MonoidHom.inl P Q) A)) 2 := rfl
  rw [h1, h2, ← groupCohomology.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The underlying linear map of the coefficient morphism is the inclusion of the invariants
`A^{1 × Q} ↪ A`. -/
theorem coe_coeffMor {k : Type u} [CommRing k] {P Q : Type u} [Group P] [Group Q]
    (A : Rep k (P × Q)) :
    (coeffMor A).hom.toLinearMap = Submodule.subtype _ := by
  rfl

/-- **The formal identity of the unramified twist**, in the coefficient ring `ℤ` (the one used
for the units of a local field): the `ℤ`-linear version of `inf_comp_res_eq_map_coeff`. -/
theorem H2_inf_comp_res_eq_map_coeff {P Q : Type} [Group P] [Group Q] (A : Rep ℤ (P × Q)) :
    (groupCohomology.infNatTrans ℤ (MonoidHom.ker (MonoidHom.fst P Q)) 2).app A ≫
      (groupCohomology.resNatTrans ℤ (G := P) (H := P × Q) (MonoidHom.inl P Q) 2).app A
    = groupCohomology.map
        ((QuotientGroup.mk' (MonoidHom.ker (MonoidHom.fst P Q))).comp (MonoidHom.inl P Q))
        (coeffMor A) 2 :=
  inf_comp_res_eq_map_coeff A

/-- The canonical map `P → (P × Q) ⧸ (1 × Q)` through which the coefficient morphism of the
unramified twist is transported is a bijection (indeed an isomorphism of groups): it identifies
the complementary factor `P = P × 1` with the quotient by the other one. -/
theorem bijective_mk'_comp_inl {P Q : Type} [Group P] [Group Q] :
    Function.Bijective ((QuotientGroup.mk' (MonoidHom.ker (MonoidHom.fst P Q))).comp
      (MonoidHom.inl P Q)) := by
  refine ⟨?_, ?_⟩
  · intro p p' h
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h
    obtain ⟨z, hz, hz'⟩ := (QuotientGroup.mk'_eq_mk' _).mp h
    have hz1 : (MonoidHom.fst P Q) z = 1 := MonoidHom.mem_ker.mp hz
    have := congrArg (MonoidHom.fst P Q) hz'
    simpa [map_mul, hz1] using this
  · intro x
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective (MonoidHom.ker (MonoidHom.fst P Q)) x
    refine ⟨MonoidHom.fst P Q γ, ?_⟩
    rw [MonoidHom.comp_apply]
    refine ((QuotientGroup.mk'_eq_mk' _).mpr ⟨(1, γ.2), ?_, ?_⟩)
    · exact MonoidHom.mem_ker.mpr rfl
    · simp

end Commons.RepresentationTheory.GroupCohomology

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false

/-- **Every unit of the base field is a norm from the (unramified) top.**

Let `q₀ ⊆ q₁ ⊆ q₂` be a tower of places of number fields `L₀ ⊆ L₁ ⊆ L₂` such that the top step
`L₂_{q₂} / L₁_{q₁}` is unramified (`e = 1`), and assume that the inertia degree `f(q₂|q₁)` divides
the ramification index `e(q₁|q₀)`.  Then every unit of `L₀_{q₀}` is the norm of a unit of
`L₂_{q₂}` over `L₁_{q₁}`:

`(L₀_{q₀})ˣ ⊆ N_{L₂_{q₂} / L₁_{q₁}}((L₂_{q₂})ˣ)`.

This is the *arithmetic* content of the residual case of Milne's divisibility step
(Milne, *CFT*, III.2) for the unramified twist.  In the application, `L₁/L₀` is totally
ramified at `q₀` (`e(q₁|q₀) = [L₁:L₀]`), `L₂/L₁` is unramified at `q₁` (`e(q₂|q₁) = 1`) with
`f(q₂|q₁) = [L₁:L₀]`, so the divisibility hypothesis holds with equality; the argument is the
explicit description of the norm group of an unramified extension
(`dvd_inertiaDeg_log_val_iff_exists_norm_of_ramificationIdx_eq_one`): a unit of `L₀` has
`v_{L₁}`-valuation a multiple of `e(q₁|q₀)`, hence (by the hypothesis) a multiple of `f(q₂|q₁)`,
and precisely those elements are norms. -/
theorem exists_norm_units_of_unramified_top_and_dvd_ramificationIdx
    {L₀ L₁ L₂ : Type*} [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂]
    [Algebra L₀ L₁] [Algebra L₁ L₂] [Algebra L₀ L₂] [IsScalarTower L₀ L₁ L₂]
    [FiniteDimensional L₀ L₁] [FiniteDimensional L₁ L₂]
    [IsGalois L₀ L₁] [IsGalois L₁ L₂]
    (q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₀))
    (q₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₁))
    (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂))
    (hq₁ : q₁.asIdeal.LiesOver q₀.asIdeal) (hq₂ : q₂.asIdeal.LiesOver q₁.asIdeal)
    (hunr : q₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₁) = 1)
    (hdvd : q₂.asIdeal.inertiaDeg (NumberField.RingOfIntegers L₁) ∣
      q₁.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₀)) :
    letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
    letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
    ∀ x : (q₀.adicCompletion L₀)ˣ,
      ∃ y : (q₂.adicCompletion L₂)ˣ,
        Algebra.norm (q₁.adicCompletion L₁) (y : q₂.adicCompletion L₂) =
          (Units.map (algebraMap (q₀.adicCompletion L₀) (q₁.adicCompletion L₁)).toMonoidHom x :
            (q₁.adicCompletion L₁)ˣ) := by
  letI : Algebra (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₀ q₁ hq₁)
  letI : Algebra (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q₂ hq₂)
  haveI : IsGalois (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    isGalois_adicCompletion q₀ q₁ hq₁
  haveI : FiniteDimensional (q₀.adicCompletion L₀) (q₁.adicCompletion L₁) :=
    module_finite_adicCompletion q₀ q₁ hq₁
  haveI : IsGalois (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    isGalois_adicCompletion q₁ q₂ hq₂
  haveI : FiniteDimensional (q₁.adicCompletion L₁) (q₂.adicCompletion L₂) :=
    module_finite_adicCompletion q₁ q₂ hq₂
  intro x
  set xE : (q₁.adicCompletion L₁)ˣ :=
    Units.map (algebraMap (q₀.adicCompletion L₀) (q₁.adicCompletion L₁)).toMonoidHom x with hxE
  have hpow : ∀ (a : Multiplicative ℤ) (k : ℕ), (a ^ k).toAdd = (k : ℤ) * a.toAdd := by
    intro a k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, show (a ^ j * a).toAdd = (a ^ j).toAdd + a.toAdd from rfl, ih]
        push_cast
        ring
  -- the logarithm of the valuation of the image of `x` in `L₁_{q₁}`
  have hlog : WithZero.log (Valued.v (R := q₁.adicCompletion L₁)
        (Γ₀ := WithZero (Multiplicative ℤ)) (xE : q₁.adicCompletion L₁)) =
      (q₁.asIdeal.ramificationIdx (NumberField.RingOfIntegers L₀) : ℤ) *
        Multiplicative.toAdd (unitsValLog (q₀.adicCompletion L₀) x) := by
    have h := congrArg Multiplicative.toAdd (unitsValLog_algebraMap q₀ q₁ hq₁ x)
    rw [← hxE] at h
    rw [unitsValLog_apply] at h
    rw [hpow] at h
    exact h
  -- the divisibility hypothesis in `ℤ`
  have hdvd' : (q₂.asIdeal.inertiaDeg (NumberField.RingOfIntegers L₁) : ℤ) ∣
      WithZero.log (Valued.v (R := q₁.adicCompletion L₁)
        (Γ₀ := WithZero (Multiplicative ℤ)) (xE : q₁.adicCompletion L₁)) := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨(c : ℤ) * Multiplicative.toAdd (unitsValLog (q₀.adicCompletion L₀) x), ?_⟩
    rw [hlog, hc]
    push_cast
    ring
  -- the explicit norm group of the unramified extension `L₂_{q₂} / L₁_{q₁}`
  obtain ⟨y, hy⟩ := (dvd_inertiaDeg_log_val_iff_exists_norm_of_ramificationIdx_eq_one
    (Q := q₁) (q := q₂) hq₂ hunr (xE : q₁.adicCompletion L₁) (Units.ne_zero xE)).mp hdvd'
  have hyne : y ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hy
    exact Units.ne_zero xE hy.symm
  refine ⟨Units.mk0 y hyne, ?_⟩
  rw [Units.val_mk0]
  exact hy


/-! ## Transport of the extension data along a pair of ring isomorphisms

The statement of the target involves three independent universes (`K`, `B`, `E`), while the
cohomological machinery used for the lower bound (`groupCohomology`, `tateCohomology`) is locked
to `Type 0`.  The lemmas below transport the field-theoretic data of an extension of fields
(`IsGalois`, `Module.Finite`, `Algebra.norm`, and the norm quotient `Bˣ ⧸ N(Eˣ)`) along a
compatible pair of ring isomorphisms `eB : B ≃+* B₀`, `eE : E ≃+* E₀` (compatible meaning
`eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)`), so that a `Type 0` statement implies the
general one.  They are the algebraic half of the universe bridge.
-/

theorem isGalois_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) [IsGalois B E] :
    IsGalois B₀ E₀ := by
  have he : RingHom.comp (algebraMap B₀ E₀) (eB : B →+* B₀) =
      RingHom.comp (eE : E →+* E₀) (algebraMap B E) := by ext x; exact (h x).symm
  haveI := Algebra.IsSeparable.of_equiv_equiv eB eE he
  haveI : Normal B₀ E₀ := Normal.of_equiv_equiv (f := eB) (g := eE) he
  exact IsGalois.mk

theorem norm_eq_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (x : E) :
    eB (Algebra.norm B x) = Algebra.norm B₀ (eE x) := by
  have he : RingHom.comp (algebraMap B₀ E₀) (eB : B →+* B₀) =
      RingHom.comp (eE : E →+* E₀) (algebraMap B E) := by ext x; exact (h x).symm
  have hx := Algebra.norm_eq_of_equiv_equiv eB eE he x
  rw [hx, RingEquiv.apply_symm_apply]

theorem moduleFinite_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) [Module.Finite B E] :
    Module.Finite B₀ E₀ := by
  let σ : B →+* B₀ := eB.toRingHom
  let f : E →ₛₗ[σ] E₀ :=
    { toFun := eE
      map_add' := fun x y => eE.map_add x y
      map_smul' := fun b x => by
        show eE (b • x) = eB b • eE x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, h b] }
  exact Module.Finite.of_surjective f eE.surjective

/-- The norm quotient `Bˣ ⧸ N_{E/B}(Eˣ)` is transported along a compatible pair of ring
isomorphisms. -/
theorem natCard_quotient_units_range_norm_eq_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E]
    [Field B₀] [Field E₀] [Algebra B E] [Algebra B₀ E₀]
    (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (B₀ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀))) := by
  have hnorm : ∀ u : Eˣ, Units.map eB.toMulEquiv (Units.map (Algebra.norm B : E →* B) u) =
      Units.map (Algebra.norm B₀ : E₀ →* B₀) (Units.map eE.toMulEquiv u) := by
    intro u
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact norm_eq_of_ringEquiv eB eE h (u : E)
  have hmap : Subgroup.map (Units.map eB.toMulEquiv)
        (MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
      exact ⟨Units.map eE.toMulEquiv u, (hnorm u).symm⟩
    · rintro ⟨v, rfl⟩
      refine ⟨Units.map (Algebra.norm B : E →* B) (Units.map eE.symm.toMulEquiv v),
        ⟨Units.map eE.symm.toMulEquiv v, rfl⟩, ?_⟩
      rw [hnorm (Units.map eE.symm.toMulEquiv v)]
      congr 1
      ext
      simp
  haveI : (MonoidHom.range (Units.map (Algebra.norm B : E →* B))).Normal :=
    Subgroup.normal_of_isMulCommutative _
  haveI : (MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀))).Normal :=
    Subgroup.normal_of_isMulCommutative _
  exact Nat.card_congr (QuotientGroup.congr _ _ (Units.mapEquiv eB.toMulEquiv) hmap).toEquiv

set_option maxHeartbeats 4000000

/-- **The requested lemma** (still conditional on the lower bound, see the module docstring). -/
theorem natCard_quotient_units_range_norm_eq_card_of_abelian_pgroup_base
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type*} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a)
    {p : ℕ} (hp : IsPGroup p (E ≃ₐ[B] E)) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (E ≃ₐ[B] E) := by
  -- The crux: the norm index theorem for every intermediate field `M` with `M/B` a `p`-group
  -- extension (`p = 0` allowed, in which case it is the full abelian case).
  have hcrux := natCard_quotient_units_range_norm_pgroup_intermediate_field (K := K) Q hcomm
  -- the top field `⊤ ↔ E` transports the `p`-group hypothesis
  have hp_top : IsPGroup p (↥(⊤ : IntermediateField B E) ≃ₐ[B] ↥(⊤ : IntermediateField B E)) :=
    IsPGroup.of_equiv hp
      (AlgEquiv.autCongr (IntermediateField.topEquiv (F := B) (E := E))).symm
  have hkey := hcrux ⊤ p hp_top
  -- transport the norm quotient along `⊤ ≃ₐ[B] E`
  have hcomp : ∀ x : B,
      (IntermediateField.topEquiv (F := B) (E := E)).toRingEquiv
        (algebraMap B ↥(⊤ : IntermediateField B E) x) = algebraMap B E x :=
    fun x => (IntermediateField.topEquiv (F := B) (E := E)).commutes x
  have hq := Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_of_ringEquiv
      (B := B) (E := ↥(⊤ : IntermediateField B E)) (B₀ := B) (E₀ := E)
      (RingEquiv.refl B) (IntermediateField.topEquiv (F := B) (E := E)).toRingEquiv hcomp
  have hcardtop : Nat.card (↥(⊤ : IntermediateField B E) ≃ₐ[B] ↥(⊤ : IntermediateField B E)) =
      Nat.card (E ≃ₐ[B] E) :=
    Nat.card_congr (AlgEquiv.autCongr (IntermediateField.topEquiv (F := B) (E := E))).toEquiv
  rw [← hq, hkey, hcardtop]
end Commons.NumberTheory.NumberField.Completion

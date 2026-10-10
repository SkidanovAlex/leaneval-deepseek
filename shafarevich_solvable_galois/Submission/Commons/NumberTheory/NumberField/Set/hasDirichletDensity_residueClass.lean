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
import Submission.Commons.NumberTheory.DirichletCharacter.primeSum_chi_isBigO_one
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_of_isBigO_primeIdealZetaSum_sub_log
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open scoped BigOperators
open Filter Asymptotics

namespace Commons.NumberTheory.NumberField.Set

open IsDedekindDomain

/-- The absolute norm of the prime ideal of `𝓞 ℚ` attached to a rational prime is that prime. -/
lemma absNorm_eq_primesEquiv (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Ideal.absNorm v.asIdeal = (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := NumberField.RingOfIntegers ℚ) v
  have hcard : Nat.card (NumberField.RingOfIntegers ℚ ⧸ v.asIdeal)
      = Nat.card (ℤ ⧸ Ideal.span ({(Rat.HeightOneSpectrum.natGenerator
          (R := NumberField.RingOfIntegers ℚ) v : ℤ)} : Set ℤ)) :=
    Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ (Rat.IsIntegralClosure.intEquiv _) h).toEquiv
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hcard]
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [Commons.NumberTheory.NumberField.DedekindZeta.absNorm_span_int]
  rfl

/-- The prime-ideal zeta sum over `ℚ` is the sum over all rational primes. -/
lemma primeIdealZetaSum_univ_rat_eq (s : ℝ) :
    NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))) s
      = ∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s)) := by
  rw [Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_univ_eq_tsum ℚ s]
  trans ∑' v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      ((((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)) : ℕ) : ℝ) ^ (-s)
  · exact tsum_congr fun v => by rw [absNorm_eq_primesEquiv]
  · exact Equiv.tsum_eq (Rat.HeightOneSpectrum.primesEquiv)
      (fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))

/-- Reindex the prime-ideal zeta sum over `ℚ` restricted to a residue class as a sum over
natural primes in that class. -/
lemma primeIdealZetaSum_residueClass_eq (n : ℕ) (a : ZMod n) (s : ℝ) :
    NumberField.Set.primeIdealZetaSum
      {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) |
        ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) = a} s
      = ∑' p : {p : Nat.Primes // ((p.1 : ℕ) : ZMod n) = a}, (((p.1 : ℕ) : ℝ) ^ (-s)) := by
  rw [NumberField.Set.primeIdealZetaSum_def]
  let e : {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) |
        ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) = a} ≃
      {p : Nat.Primes // ((p.1 : ℕ) : ZMod n) = a} :=
    Equiv.subtypeEquiv (Rat.HeightOneSpectrum.primesEquiv) (fun v => by
      simp only [Set.mem_ofPred_eq]
      rw [absNorm_eq_primesEquiv v])
  rw [← Equiv.tsum_eq e.symm (fun v : {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) |
        ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) = a} => (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s))]
  refine tsum_congr fun p => ?_
  have hcoe : (e.symm p).1 = Rat.HeightOneSpectrum.primesEquiv.symm p.1 := rfl
  rw [hcoe, absNorm_eq_primesEquiv, Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply]

lemma one_char_apply (n : ℕ) (x : ZMod n) :
    (1 : DirichletCharacter ℂ n) x = if IsUnit x then 1 else 0 := by
  classical
  by_cases h : IsUnit x
  · rw [if_pos h, MulChar.one_apply h]
  · rw [if_neg h, MulChar.map_nonunit _ h]

lemma summable_primes_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => ((p.1 : ℕ) : ℝ) ^ (-s)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    (Real.summable_nat_rpow).mpr (by linarith)
  exact h.subtype _

lemma summable_primes_rpow_neg_complex {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) :=
  (summable_primes_rpow_neg hs).map Complex.ofRealCLM Complex.continuous_ofReal

/-- The complex character-orthogonality identity for the prime sum in a residue class,
in indicator form over all rational primes. -/
lemma class_indicator_identity (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) {s : ℝ} (hs : 1 < s) :
    (n.totient : ℂ) * (∑' p : Nat.Primes,
        (if (a : ZMod n) = ((p.1 : ℕ) : ZMod n) then ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) else 0))
      = ∑ χ : DirichletCharacter ℂ n,
          χ ((a : ZMod n))⁻¹
            * (∑' p : Nat.Primes, χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
  classical
  have hsumm_all : Summable (fun p : Nat.Primes => ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) :=
    summable_primes_rpow_neg_complex hs
  have hsumm : ∀ χ : DirichletCharacter ℂ n,
      Summable (fun p : Nat.Primes => χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
    intro χ
    refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))
      (f := fun p : Nat.Primes => χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      (summable_primes_rpow_neg hs) (fun p => ?_)
    rw [norm_mul]
    have hχ : ‖χ ((p.1 : ℕ) : ZMod n)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hf : 0 ≤ ((p.1 : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc ‖χ ((p.1 : ℕ) : ZMod n)‖ * ‖((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)‖
        ≤ 1 * ‖((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)‖ := mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
      _ = (((p.1 : ℕ) : ℝ) ^ (-s)) := by
          rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
  symm
  calc ∑ χ : DirichletCharacter ℂ n,
          χ ((a : ZMod n))⁻¹
            * (∑' p : Nat.Primes, χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      = ∑ χ : DirichletCharacter ℂ n, ∑' p : Nat.Primes,
          χ ((a : ZMod n))⁻¹ * (χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [tsum_mul_left]
    _ = ∑' p : Nat.Primes, ∑ χ : DirichletCharacter ℂ n,
          χ ((a : ZMod n))⁻¹ * (χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
        rw [Summable.tsum_finsetSum]
        intro χ _
        exact (hsumm χ).mul_left _
    _ = ∑' p : Nat.Primes,
          (∑ χ : DirichletCharacter ℂ n, χ ((a : ZMod n))⁻¹ * χ ((p.1 : ℕ) : ZMod n))
            * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
        refine tsum_congr (fun p => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun χ _ => by ring)
    _ = ∑' p : Nat.Primes,
          (if (a : ZMod n) = ((p.1 : ℕ) : ZMod n) then (n.totient : ℂ) else 0)
            * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
        refine tsum_congr (fun p => ?_)
        rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit ((p.1 : ℕ) : ZMod n)]
    _ = (n.totient : ℂ) * ∑' p : Nat.Primes,
          (if (a : ZMod n) = ((p.1 : ℕ) : ZMod n) then ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) else 0) := by
        rw [← tsum_mul_left]
        refine tsum_congr (fun p => ?_)
        by_cases hp : (a : ZMod n) = ((p.1 : ℕ) : ZMod n) <;> simp [hp]


/-- Splitting `∑_p p^{-s}` into the primes coprime to `n` and those dividing `n`. -/
lemma split_sum (n : ℕ) [NeZero n] {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s)))
      = (∑' p : Nat.Primes, (if IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0))
        + (∑' p : Nat.Primes, (if IsUnit ((p.1 : ℕ) : ZMod n) then 0 else (((p.1 : ℕ) : ℝ) ^ (-s)))) := by
  have hA : Summable (fun p : Nat.Primes =>
      (if IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0)) := by
    refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))
      (f := fun p : Nat.Primes =>
        (if IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0))
      (summable_primes_rpow_neg hs) (fun p => ?_)
    rw [Real.norm_eq_abs]
    have hf : 0 ≤ ((p.1 : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    by_cases h : IsUnit ((p.1 : ℕ) : ZMod n)
    · rw [if_pos h, abs_of_nonneg hf]
    · rw [if_neg h, abs_zero]; exact hf
  have hB : Summable (fun p : Nat.Primes =>
      (if IsUnit ((p.1 : ℕ) : ZMod n) then 0 else (((p.1 : ℕ) : ℝ) ^ (-s)))) := by
    refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))
      (f := fun p : Nat.Primes =>
        (if IsUnit ((p.1 : ℕ) : ZMod n) then 0 else (((p.1 : ℕ) : ℝ) ^ (-s))))
      (summable_primes_rpow_neg hs) (fun p => ?_)
    rw [Real.norm_eq_abs]
    have hf : 0 ≤ ((p.1 : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    by_cases h : IsUnit ((p.1 : ℕ) : ZMod n)
    · rw [if_pos h, abs_zero]; exact hf
    · rw [if_neg h, abs_of_nonneg hf]
  rw [← Summable.tsum_add hA hB]
  refine tsum_congr fun p => ?_
  by_cases h : IsUnit ((p.1 : ℕ) : ZMod n) <;> simp [h]

/-- The real part of the `χ = 1` term is the sum over primes coprime to `n`. -/
lemma W_one_re (n : ℕ) [NeZero n] {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, (1 : DirichletCharacter ℂ n) ((p.1 : ℕ) : ZMod n)
        * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)).re
      = ∑' p : Nat.Primes,
          (if IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0) := by
  have hsumm : Summable (fun p : Nat.Primes =>
      (1 : DirichletCharacter ℂ n) ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
    refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))
      (f := fun p : Nat.Primes => (1 : DirichletCharacter ℂ n) ((p.1 : ℕ) : ZMod n)
        * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) (summable_primes_rpow_neg hs) (fun p => ?_)
    rw [norm_mul]
    have hχ : ‖(1 : DirichletCharacter ℂ n) ((p.1 : ℕ) : ZMod n)‖ ≤ 1 :=
      DirichletCharacter.norm_le_one _ _
    have hf : 0 ≤ ((p.1 : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc ‖(1 : DirichletCharacter ℂ n) ((p.1 : ℕ) : ZMod n)‖ * ‖((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)‖
        ≤ 1 * ‖((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
      _ = (((p.1 : ℕ) : ℝ) ^ (-s)) := by
          rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
  rw [Complex.re_tsum hsumm]
  refine tsum_congr fun p => ?_
  rw [one_char_apply]
  by_cases h : IsUnit ((p.1 : ℕ) : ZMod n)
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]; simp

set_option backward.isDefEq.respectTransparency false in
lemma not_isUnit_iff_dvd (n : ℕ) (p : Nat.Primes) :
    ¬ IsUnit (((p.1 : ℕ) : ZMod n)) ↔ p.1 ∣ n := by
  rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd p.2, not_not]

set_option backward.isDefEq.respectTransparency false in
lemma mem_badPrimes (n : ℕ) [NeZero n] (p : Nat.Primes) :
    p ∈ n.primeFactors.attach.image
        (fun q => (⟨q.1, (Nat.mem_primeFactors.mp q.2).1⟩ : Nat.Primes)) ↔ p.1 ∣ n := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, _, hq⟩
    have hq1 : q.1 = p.1 := by rw [← hq]
    rw [← hq1]
    exact (Nat.mem_primeFactors.mp q.2).2.1
  · intro h
    refine ⟨⟨p.1, Nat.Prime.mem_primeFactors p.2 h (NeZero.ne n)⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

set_option backward.isDefEq.respectTransparency false in
lemma sum_bad_le (n : ℕ) [NeZero n] {s : ℝ} (hs : 0 ≤ s) :
    (∑' p : Nat.Primes,
        (if IsUnit ((p.1 : ℕ) : ZMod n) then 0 else (((p.1 : ℕ) : ℝ) ^ (-s))))
      ≤ (n.primeFactors.card : ℝ) := by
  classical
  have hbad : ∀ p : Nat.Primes,
      (if IsUnit ((p.1 : ℕ) : ZMod n) then (0:ℝ) else (((p.1 : ℕ) : ℝ) ^ (-s)))
        = (if ¬ IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0) := by
    intro p
    by_cases h : IsUnit ((p.1 : ℕ) : ZMod n) <;> simp [h]
  rw [tsum_congr hbad]
  set bad : Finset Nat.Primes := n.primeFactors.attach.image
      (fun q => (⟨q.1, (Nat.mem_primeFactors.mp q.2).1⟩ : Nat.Primes)) with hbaddef
  rw [tsum_eq_sum (s := bad) (fun p hp => by
    rw [if_neg]
    rw [not_isUnit_iff_dvd]
    intro hd
    exact hp (by rw [hbaddef, mem_badPrimes]; exact hd))]
  calc ∑ p ∈ bad, (if ¬ IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0)
      ≤ ∑ _p ∈ bad, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp1 : (1 : ℝ) ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast p.2.one_le
        by_cases h : ¬ IsUnit ((p.1 : ℕ) : ZMod n)
        · rw [if_pos h]; exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
        · rw [if_neg h]; norm_num
    _ = (bad.card : ℝ) := by simp
    _ ≤ (n.primeFactors.card : ℝ) := by
        have : bad.card ≤ n.primeFactors.card := by
          rw [hbaddef]
          calc _ ≤ (n.primeFactors.attach).card := Finset.card_image_le
            _ = n.primeFactors.card := Finset.card_attach
        exact_mod_cast this


lemma primeSum_all_isBigO :
    (fun s : ℝ => (∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s)))
        - Real.log (1 / (s - 1)))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℝ)) := by
  refine (Commons.NumberTheory.NumberField.Set.isBigO_primeIdealZetaSum_sub_log ℚ).congr'
    (Filter.EventuallyEq.of_eq (funext fun s => ?_)) Filter.EventuallyEq.rfl
  rw [primeIdealZetaSum_univ_rat_eq]

/-- The Dirichlet-density asymptotic of the indicator of the residue class, reduced to the
character orthogonality identity and the boundedness of the nontrivial prime sums. -/
theorem primeSum_indicator_isBigO (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    (fun s : ℝ => (∑' p : Nat.Primes,
        (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0))
        - (n.totient : ℝ)⁻¹ * Real.log (1 / (s - 1)))
      =O[nhdsWithin (1:ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1:ℝ)) := by
  classical
  have hSne : (fun s : ℝ => ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
      (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n) * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re)
      =O[nhdsWithin (1:ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1:ℝ)) := by
    have hsum : (∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
        fun s : ℝ => (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
          * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re)
        =O[nhdsWithin (1:ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1:ℝ)) := by
      apply IsBigO.sum
      intro χ hχ
      have hχne : χ ≠ 1 := by simpa using hχ
      have h1 : (fun s : ℝ => (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re)
          =O[nhdsWithin (1:ℝ) (Set.Ioi 1)]
            (fun s : ℝ => ‖χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖) := by
        apply IsBigO.of_bound 1
        filter_upwards with s
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (norm_nonneg _), one_mul]
        exact Complex.abs_re_le_norm _
      have h2 : (fun s : ℝ => ‖χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖)
          =O[nhdsWithin (1:ℝ) (Set.Ioi 1)]
            (fun s : ℝ => ‖(∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖) := by
        apply IsBigO.of_bound 1
        filter_upwards with s
        simp only [one_mul, Real.norm_of_nonneg (norm_nonneg _)]
        calc ‖χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖
            ≤ ‖χ ((a:ZMod n))⁻¹‖ * ‖(∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖ := norm_mul_le _ _
          _ ≤ 1 * ‖(∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖ :=
              mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (norm_nonneg _)
          _ = _ := one_mul _
      exact h1.trans (h2.trans ((Commons.NumberTheory.DirichletCharacter.primeSum_chi_isBigO_one
        χ hχne).norm_left))
    refine hsum.congr' (Filter.EventuallyEq.of_eq (funext fun s => ?_)) Filter.EventuallyEq.rfl
    simp only [Finset.sum_apply]
  -- Extract the constant for the all-primes sum.
  obtain ⟨Call, hCall⟩ : ∃ Call : ℝ, ∀ᶠ s in nhdsWithin (1:ℝ) (Set.Ioi 1),
      ‖(∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1))‖ ≤ Call := by
    have h := primeSum_all_isBigO
    rw [Asymptotics.isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by filter_upwards [hc] with s hs; simpa using hs⟩
  -- Extract constants bounding the nontrivial-character contributions.
  obtain ⟨Cne, hCne⟩ : ∃ Cne : ℝ, ∀ᶠ s in nhdsWithin (1:ℝ) (Set.Ioi 1),
      ‖∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
        (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
          * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re‖ ≤ Cne := by
    have h := hSne
    rw [Asymptotics.isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by filter_upwards [hc] with s hs; simpa using hs⟩
  -- Assemble.
  have hφpos : 0 < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos n)
  refine IsBigO.of_bound ((n.totient : ℝ)⁻¹ * (Call + (n.primeFactors.card : ℝ) + Cne)) ?_
  filter_upwards [self_mem_nhdsWithin, hCall, hCne] with s hs1 hCall' hCne'
  have hs : 1 < s := Set.mem_Ioi.mp hs1
  have hs0 : 0 ≤ s := by linarith
  -- identity
  have hid := class_indicator_identity n a hs
  -- real part of the identity
  have hPS : (∑' p : Nat.Primes, (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then
        ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ) else 0)).re
      = ∑' p : Nat.Primes, (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0) := by
    have hsumm : Summable (fun p : Nat.Primes => (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then
        ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ) else 0)) := by
      refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))
        (f := fun p : Nat.Primes => (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then
          ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ) else 0)) (summable_primes_rpow_neg hs) (fun p => ?_)
      have hf : 0 ≤ ((p.1:ℕ):ℝ)^(-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      by_cases h : (a : ZMod n) = ((p.1:ℕ):ZMod n)
      · rw [if_pos h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
      · rw [if_neg h, norm_zero]; exact hf
    rw [Complex.re_tsum hsumm]
    refine tsum_congr fun p => ?_
    by_cases h : (a : ZMod n) = ((p.1:ℕ):ZMod n) <;> simp [h]
  have hidre : (n.totient : ℝ) * (∑' p : Nat.Primes, (if (a : ZMod n) = ((p.1:ℕ):ZMod n)
        then (((p.1:ℕ):ℝ)^(-s)) else 0))
      = ∑ χ : DirichletCharacter ℂ n,
          (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re := by
    have h := congrArg Complex.re hid
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, hPS] at h
    rw [← Complex.reCLM_apply, map_sum Complex.reCLM] at h
    exact h
  -- split the finite sum
  have hsplit : ∑ χ : DirichletCharacter ℂ n,
        (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
          * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re
      = ((1 : DirichletCharacter ℂ n) ((a:ZMod n))⁻¹
          * (∑' p : Nat.Primes, (1 : DirichletCharacter ℂ n) ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re
        + ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
            (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re := by
    rw [Fintype.sum_eq_add_sum_compl 1]
  -- the trivial term
  have hone : ((1 : DirichletCharacter ℂ n) ((a:ZMod n))⁻¹
        * (∑' p : Nat.Primes, (1 : DirichletCharacter ℂ n) ((p.1:ℕ):ZMod n)
          * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re
      = (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0)) := by
    have h1 : (1 : DirichletCharacter ℂ n) ((a:ZMod n))⁻¹ = 1 := by
      rw [ZMod.inv_coe_unit, MulChar.one_apply (Units.isUnit a⁻¹)]
    rw [h1, one_mul]
    exact W_one_re n hs
  -- split the all-primes sum
  have hsplit2 := split_sum (n := n) hs
  -- bad bound
  have hbad : (∑' p : Nat.Primes,
        (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s)))) ≤ (n.primeFactors.card : ℝ) :=
    sum_bad_le n hs0
  -- assemble the pointwise bound
  have key : (n.totient : ℝ)
        * (∑' p : Nat.Primes, (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0))
        - Real.log (1 / (s - 1))
      = ((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
        - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))
        + ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
            (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re := by
    rw [hidre, hsplit, hone]
    have hsun : (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0))
        = (∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s)))
          - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s)))) := by
      linarith [hsplit2]
    rw [hsun]; ring
  rw [Real.norm_eq_abs, norm_one, mul_one]
  have hA : |(∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1))| ≤ Call := by
    rw [← Real.norm_eq_abs]; exact hCall'
  have hB0 : 0 ≤ (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s)))) := by
    refine tsum_nonneg fun p => ?_
    by_cases h : IsUnit ((p.1:ℕ):ZMod n)
    · simp [h]
    · simp only [h, if_false]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hB : |(∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))|
      ≤ (n.primeFactors.card : ℝ) := by
    rw [abs_of_nonneg hB0]; exact hbad
  have hC : |∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
        (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
          * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re| ≤ Cne := by
    rw [← Real.norm_eq_abs]; exact hCne'
  have hb : |((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
        - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))
        + ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
            (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re|
      ≤ Call + (n.primeFactors.card : ℝ) + Cne := by
    have hsub : |((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
        - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))|
        ≤ Call + (n.primeFactors.card : ℝ) := by
      have htri : |((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
          - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))|
          ≤ |(∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1))|
            + |(∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))| := by
        rw [abs_le]
        constructor <;>
          linarith [neg_le_abs ((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1))),
            le_abs_self ((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1))),
            neg_le_abs (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s)))),
            le_abs_self (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))]
      linarith
    calc |((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
          - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))
          + ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
              (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
                * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re|
        ≤ |((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
            - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))|
          + |∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
              (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
                * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re| := abs_add_le _ _
      _ ≤ (Call + (n.primeFactors.card : ℝ)) + Cne := add_le_add hsub hC
      _ = Call + (n.primeFactors.card : ℝ) + Cne := by ring
  rw [show (∑' p : Nat.Primes, (if (a:ZMod n) = ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0))
      - (n.totient:ℝ)⁻¹ * Real.log (1/(s-1))
      = (n.totient:ℝ)⁻¹ * ((n.totient:ℝ) * (∑' p : Nat.Primes,
          (if (a:ZMod n) = ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0))
          - Real.log (1/(s-1))) from by
      field_simp]
  rw [abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hφpos)), key]
  exact mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.mpr hφpos))


/-- The residue-class sum over `Nat.Primes` (as a subtype) equals the indicator sum. -/
lemma subtype_eq_indicator (n : ℕ) (a : ZMod n) (s : ℝ) :
    (∑' p : {p : Nat.Primes // ((p.1 : ℕ) : ZMod n) = a}, (((p.1 : ℕ) : ℝ) ^ (-s)))
      = ∑' p : Nat.Primes, (if ((p.1 : ℕ) : ZMod n) = a then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0) := by
  let G : Nat.Primes → ℝ := fun p => (((p.1 : ℕ) : ℝ) ^ (-s))
  change (∑' p : {p : Nat.Primes // ((p.1 : ℕ) : ZMod n) = a}, G p)
      = ∑' p : Nat.Primes, (if ((p.1 : ℕ) : ZMod n) = a then G p else 0)
  rw [show (∑' p : {p : Nat.Primes // ((p.1 : ℕ) : ZMod n) = a}, G p)
      = ∑' p : {p : Nat.Primes // p ∈ {q : Nat.Primes | ((q.1 : ℕ) : ZMod n) = a}}, G p from rfl]
  rw [tsum_subtype]
  refine tsum_congr fun p => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- **Dirichlet's theorem on primes in arithmetic progressions, Dirichlet-density form.**

The set of rational primes `p` with `p ≡ a (mod n)` has Dirichlet density `1/φ(n)`. -/
theorem hasDirichletDensity_residueClass (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    NumberField.Set.HasDirichletDensity
      {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) |
        ((Ideal.absNorm p.asIdeal : ℕ) : ZMod n) = (a : ZMod n)}
      ((Nat.totient n : ℝ)⁻¹) := by
  refine Commons.NumberTheory.NumberField.Set.hasDirichletDensity_of_isBigO_primeIdealZetaSum_sub_log ?_
  refine (primeSum_indicator_isBigO n a).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards with s
  rw [primeIdealZetaSum_residueClass_eq, subtype_eq_indicator]
  congr 1
  refine tsum_congr fun p => ?_
  by_cases h : (a : ZMod n) = ((p.1 : ℕ) : ZMod n)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

end Commons.NumberTheory.NumberField.Set

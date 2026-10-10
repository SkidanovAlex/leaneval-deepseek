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
import Submission.Commons.NumberTheory.Nat.omega_color_sum_le_harmonic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

open scoped _root_.NumberField nonZeroDivisors

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {K : Type*} [Field K] [NumberField K]

lemma primesOverFinset_card_le (p : ℕ) [Fact (Nat.Prime p)] :
    (IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (NumberField.RingOfIntegers K)).card ≤ Module.finrank ℚ K := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpZ_ne : pZ ≠ ⊥ := by
    exact (Ideal.span_singleton_eq_bot).not.mpr hp0
  have hpZ_max : pZ.IsMaximal := by
    have hpZ_prime : pZ.IsPrime := by
      exact (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))
    exact hpZ_prime.isMaximal hpZ_ne
  have h := Ideal.card_primesOverFinset_le_finrank (R := ℤ) (S := NumberField.RingOfIntegers K) (K := ℚ) (L := K)
    (p := pZ) hpZ_ne
  simpa [NumberField.RingOfIntegers.rank K] using h

noncomputable def primesOverIndex (p : ℕ) [Fact (Nat.Prime p)] :
    {P : Ideal (NumberField.RingOfIntegers K) // P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (NumberField.RingOfIntegers K)} ↪ Fin (Module.finrank ℚ K) := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let s : Finset (Ideal (NumberField.RingOfIntegers K)) := IsDedekindDomain.primesOverFinset pZ (NumberField.RingOfIntegers K)
  have hcard : Fintype.card {P : Ideal (NumberField.RingOfIntegers K) // P ∈ s} ≤ Fintype.card (Fin (Module.finrank ℚ K)) := by
    simpa using primesOverFinset_card_le (K := K) p
  exact Classical.choice (Function.Embedding.nonempty_of_card_le (α := {P : Ideal (NumberField.RingOfIntegers K) // P ∈ s}) (β := Fin (Module.finrank ℚ K)) hcard)

noncomputable def primeIndex (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Fin (Module.finrank ℚ K) := by
  classical
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  haveI : P.IsPrime := hP
  haveI : NeZero P := ⟨hP0⟩
  have hp : Nat.Prime p := by
    dsimp [p]
    exact Nat.absNorm_under_prime P
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hpZ_ne : pZ ≠ ⊥ := by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact (Ideal.span_singleton_eq_bot).not.mpr hp0
  have hpZ_max : pZ.IsMaximal := by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpZ_prime : pZ.IsPrime := by
      exact (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)
    exact hpZ_prime.isMaximal hpZ_ne
  let s : Finset (Ideal (NumberField.RingOfIntegers K)) := IsDedekindDomain.primesOverFinset pZ (NumberField.RingOfIntegers K)
  have hmem : P ∈ s := by
    have hpr : P ∈ pZ.primesOver (NumberField.RingOfIntegers K) := ⟨hP, by
      simpa [p, pZ] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))⟩
    exact (IsDedekindDomain.mem_primesOverFinset_iff hpZ_ne (B := NumberField.RingOfIntegers K)).mpr hpr
  exact (primesOverIndex (K := K) p) ⟨P, hmem⟩

lemma primeIndex_underlying_liesOver (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)) := by
  simpa using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))

lemma primeIndex_underlying_prime (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Nat.Prime (Ideal.absNorm (Ideal.under ℤ P)) := by
  haveI : P.IsPrime := hP
  haveI : NeZero P := ⟨hP0⟩
  exact Nat.absNorm_under_prime P

noncomputable def idealToTuple (I : (Ideal (NumberField.RingOfIntegers K))⁰) : Fin (Module.finrank ℚ K) → ℕ := by
  classical
  let J : Ideal (NumberField.RingOfIntegers K) := I
  have hJ : J ≠ ⊥ := by
    dsimp [J]
    simpa using (nonZeroDivisors.coe_ne_zero I)
  let fac : Multiset (Ideal (NumberField.RingOfIntegers K)) := UniqueFactorizationMonoid.normalizedFactors J
  exact fun i => ∏ P : {P : Ideal (NumberField.RingOfIntegers K) // P ∈ fac.toFinset},
    let Q : Ideal (NumberField.RingOfIntegers K) := P.1
    let hPs : Q ∈ fac.toFinset := P.2
    let hPfac : Q ∈ fac := Multiset.mem_toFinset.mp hPs
    let hPprime : Q.IsPrime := ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).1
    let hP0 : Q ≠ ⊥ := by
      intro hPbot
      have hJle : J ≤ ⊥ := by
        simpa [hPbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).2
      exact hJ (le_bot_iff.mp hJle)
    if primeIndex (K := K) Q hPprime hP0 = i then Ideal.absNorm Q ^ fac.count Q else 1

lemma idealToTuple_prod (I : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ∏ i : Fin (Module.finrank ℚ K), idealToTuple I i = Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) := by
  classical
  let J : Ideal (NumberField.RingOfIntegers K) := I
  have hJ : J ≠ ⊥ := by
    dsimp [J]
    simpa using (nonZeroDivisors.coe_ne_zero I)
  let fac : Multiset (Ideal (NumberField.RingOfIntegers K)) := UniqueFactorizationMonoid.normalizedFactors J
  have hfac_prod : fac.prod = J := by
    dsimp [fac]
    exact Ideal.prod_normalizedFactors_eq_self hJ
  have habs : Ideal.absNorm J = (fac.map (fun P => Ideal.absNorm P)).prod := by
    rw [← hfac_prod]
    exact map_multiset_prod (Ideal.absNorm) fac
  calc
    ∏ i : Fin (Module.finrank ℚ K), idealToTuple I i
        = ∏ i : Fin (Module.finrank ℚ K), ∏ P : {P : Ideal (NumberField.RingOfIntegers K) // P ∈ fac.toFinset},
            (if primeIndex (K := K) P.1 (by
                have hPfac : P.1 ∈ fac := Multiset.mem_toFinset.mp P.2
                exact ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).1)
              (by
                have hPfac : P.1 ∈ fac := Multiset.mem_toFinset.mp P.2
                intro hPbot
                have hJle : J ≤ ⊥ := by
                  simpa [hPbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).2
                exact hJ (le_bot_iff.mp hJle)) = i then
              Ideal.absNorm P.1 ^ fac.count P.1 else 1) := by
          simp [idealToTuple, J, fac]
    _ = ∏ P : {P : Ideal (NumberField.RingOfIntegers K) // P ∈ fac.toFinset},
          ∏ i : Fin (Module.finrank ℚ K),
            (if primeIndex (K := K) P.1 (by
                have hPfac : P.1 ∈ fac := Multiset.mem_toFinset.mp P.2
                exact ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).1)
              (by
                have hPfac : P.1 ∈ fac := Multiset.mem_toFinset.mp P.2
                intro hPbot
                have hJle : J ≤ ⊥ := by
                  simpa [hPbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).2
                exact hJ (le_bot_iff.mp hJle)) = i then
              Ideal.absNorm P.1 ^ fac.count P.1 else 1) := by
          rw [Finset.prod_comm]
    _ = ∏ P : {P : Ideal (NumberField.RingOfIntegers K) // P ∈ fac.toFinset},
          Ideal.absNorm P.1 ^ fac.count P.1 := by
          apply Finset.prod_congr rfl
          intro P hP
          let Q : Ideal (NumberField.RingOfIntegers K) := P.1
          have hPfac : Q ∈ fac := Multiset.mem_toFinset.mp P.2
          have hPprime : Q.IsPrime := ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).1
          have hP0 : Q ≠ ⊥ := by
            intro hPbot
            have hJle : J ≤ ⊥ := by
              simpa [hPbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).2
            exact hJ (le_bot_iff.mp hJle)
          change (∏ i : Fin (Module.finrank ℚ K),
              (if primeIndex (K := K) Q hPprime hP0 = i then Ideal.absNorm Q ^ fac.count Q else 1))
              = Ideal.absNorm Q ^ fac.count Q
          rw [Finset.prod_ite_eq]
          simp
    _ = ∏ P ∈ fac.toFinset, Ideal.absNorm P ^ fac.count P := by
          exact (Finset.prod_coe_sort fac.toFinset (fun P => Ideal.absNorm P ^ fac.count P))
    _ = (fac.map (fun P => Ideal.absNorm P)).prod := by
          rw [Finset.prod_multiset_map_count]
    _ = Ideal.absNorm J := habs.symm
    _ = Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) := by simp [J]

lemma idealToTuple_one_le (I : (Ideal (NumberField.RingOfIntegers K))⁰) (i : Fin (Module.finrank ℚ K)) :
    1 ≤ idealToTuple I i := by
  classical
  let J : Ideal (NumberField.RingOfIntegers K) := I
  have hJ : J ≠ ⊥ := by
    dsimp [J]
    simpa using (nonZeroDivisors.coe_ne_zero I)
  let fac : Multiset (Ideal (NumberField.RingOfIntegers K)) := UniqueFactorizationMonoid.normalizedFactors J
  dsimp [idealToTuple]
  apply Finset.one_le_prod₀
  intro P hP
  let Q : Ideal (NumberField.RingOfIntegers K) := P.1
  have hPs : Q ∈ fac.toFinset := P.2
  have hPfac : Q ∈ fac := Multiset.mem_toFinset.mp hPs
  have hPprime : Q.IsPrime := ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).1
  have hP0 : Q ≠ ⊥ := by
    intro hPbot
    have hJle : J ≤ ⊥ := by
      simpa [hPbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp hPfac).2
    exact hJ (le_bot_iff.mp hJle)
  change 1 ≤ if primeIndex (K := K) Q hPprime hP0 = i then Ideal.absNorm Q ^ fac.count Q else 1
  by_cases h : primeIndex (K := K) Q hPprime hP0 = i
  · simp [h]
    apply one_le_pow₀
    exact Nat.succ_le_iff.mpr (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero hP0))
  · simp [h]

lemma idealToTuple_mem_tupleFinset (A : ℕ)
    (I : {I : (Ideal (NumberField.RingOfIntegers K))⁰ // Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ A}) :
    idealToTuple I.1 ∈ Commons.NumberTheory.Nat.tupleFinset (Module.finrank ℚ K) A := by
  classical
  rw [Commons.NumberTheory.Nat.mem_tupleFinset]
  constructor
  · intro i
    have h1 : 1 ≤ idealToTuple I.1 i := idealToTuple_one_le I.1 i
    have hle : idealToTuple I.1 i ≤ ∏ j : Fin (Module.finrank ℚ K), idealToTuple I.1 j := by
      have hsingle := Finset.single_le_prod' (s := (Finset.univ : Finset (Fin (Module.finrank ℚ K))))
        (f := idealToTuple I.1) (fun j hj => idealToTuple_one_le I.1 j) (a := i) (Finset.mem_univ i)
      simpa using hsingle
    have hprod : (∏ j : Fin (Module.finrank ℚ K), idealToTuple I.1 j) ≤ A := by
      rw [idealToTuple_prod I.1]
      exact I.2
    exact Finset.mem_Icc.mpr ⟨h1, le_trans hle hprod⟩
  · rw [idealToTuple_prod I.1]
    exact I.2

lemma underlying_absNorm_eq_of_liesOver {P : Ideal (NumberField.RingOfIntegers K)} {p : ℕ}
    (hp : Nat.Prime p) (hPl : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    Ideal.absNorm (Ideal.under ℤ P) = p := by
  classical
  let m : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  have hlie_m : P.LiesOver (Ideal.span ({(m : ℤ)} : Set ℤ)) := by
    simpa [m] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))
  have hm_under : Ideal.span ({(m : ℤ)} : Set ℤ) = Ideal.under ℤ P := by
    exact (Ideal.liesOver_iff P (Ideal.span ({(m : ℤ)} : Set ℤ))).mp hlie_m
  have hp_under : Ideal.span ({(p : ℤ)} : Set ℤ) = Ideal.under ℤ P := by
    exact (Ideal.liesOver_iff P (Ideal.span ({(p : ℤ)} : Set ℤ))).mp hPl
  have hsp : Ideal.span ({(m : ℤ)} : Set ℤ) = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    rw [hm_under, hp_under]
  have hle_mp : Ideal.span ({(m : ℤ)} : Set ℤ) ≤ Ideal.span ({(p : ℤ)} : Set ℤ) := le_of_eq hsp
  have hle_pm : Ideal.span ({(p : ℤ)} : Set ℤ) ≤ Ideal.span ({(m : ℤ)} : Set ℤ) := le_of_eq hsp.symm
  have hdiv_pm : (p : ℤ) ∣ (m : ℤ) := by
    exact (Ideal.span_singleton_le_span_singleton.mp hle_mp)
  have hdiv_mp : (m : ℤ) ∣ (p : ℤ) := by
    exact (Ideal.span_singleton_le_span_singleton.mp hle_pm)
  have hdiv_pm_nat : p ∣ m := Int.natCast_dvd_natCast.mp hdiv_pm
  have hdiv_mp_nat : m ∣ p := Int.natCast_dvd_natCast.mp hdiv_mp
  exact Nat.dvd_antisymm hdiv_mp_nat hdiv_pm_nat

lemma primeIndex_inj_of_liesOver {P Q : Ideal (NumberField.RingOfIntegers K)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥)
    {p : ℕ} (hp : Nat.Prime p)
    (hPl : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (hQl : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    (h : primeIndex (K := K) P hP hP0 = primeIndex (K := K) Q hQ hQ0) :
    P = Q := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpZ_ne : pZ ≠ ⊥ := by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact (Ideal.span_singleton_eq_bot).not.mpr hp0
  have hmemP : P ∈ IsDedekindDomain.primesOverFinset pZ (NumberField.RingOfIntegers K) := by
    have hpr : P ∈ pZ.primesOver (NumberField.RingOfIntegers K) := ⟨hP, hPl⟩
    exact (IsDedekindDomain.mem_primesOverFinset_iff hpZ_ne (B := NumberField.RingOfIntegers K)).mpr hpr
  have hmemQ : Q ∈ IsDedekindDomain.primesOverFinset pZ (NumberField.RingOfIntegers K) := by
    have hpr : Q ∈ pZ.primesOver (NumberField.RingOfIntegers K) := ⟨hQ, hQl⟩
    exact (IsDedekindDomain.mem_primesOverFinset_iff hpZ_ne (B := NumberField.RingOfIntegers K)).mpr hpr
  have hPidx : primeIndex (K := K) P hP hP0 = (primesOverIndex (K := K) p) ⟨P, hmemP⟩ := by
    have hmp : Ideal.absNorm (Ideal.under ℤ P) = p := underlying_absNorm_eq_of_liesOver hp hPl
    subst p
    unfold primeIndex
    rfl
  have hQidx : primeIndex (K := K) Q hQ hQ0 = (primesOverIndex (K := K) p) ⟨Q, hmemQ⟩ := by
    have hmq : Ideal.absNorm (Ideal.under ℤ Q) = p := underlying_absNorm_eq_of_liesOver hp hQl
    subst p
    unfold primeIndex
    rfl
  have hemb : (primesOverIndex (K := K) p) ⟨P, hmemP⟩ = (primesOverIndex (K := K) p) ⟨Q, hmemQ⟩ := by
    rw [← hPidx, ← hQidx]
    exact h
  have hsub := (primesOverIndex (K := K) p).injective hemb
  simpa using congrArg Subtype.val hsub

lemma absNorm_pow_factorization_eq (P : Ideal (NumberField.RingOfIntegers K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (c : ℕ) :
    (Ideal.absNorm P ^ c).factorization (Ideal.absNorm (Ideal.under ℤ P)) =
      (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)).inertiaDeg' P * c := by
  classical
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp : Nat.Prime p := by
    dsimp [p]
    haveI : P.IsPrime := hP
    haveI : NeZero P := ⟨hP0⟩
    exact Nat.absNorm_under_prime P
  have hPl : P.LiesOver pZ := by
    simpa [p, pZ] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))
  have hnorm : Ideal.absNorm P = p ^ (pZ.inertiaDeg' P) := by
    exact Ideal.absNorm_eq_pow_inertiaDeg' (R := NumberField.RingOfIntegers K) P hp
  have hpow : (Ideal.absNorm P ^ c).factorization p = (p ^ (pZ.inertiaDeg' P * c)).factorization p := by
    rw [hnorm, pow_mul]
  rw [hpow, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]

lemma absNorm_pow_factorization_eq_zero_of_not_liesOver {Q : Ideal (NumberField.RingOfIntegers K)}
    (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) {p : ℕ} (hp : Nat.Prime p)
    (hnot : ¬ Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) (c : ℕ) :
    (Ideal.absNorm Q ^ c).factorization p = 0 := by
  classical
  let q : ℕ := Ideal.absNorm (Ideal.under ℤ Q)
  have hq : Nat.Prime q := by
    dsimp [q]
    haveI : Q.IsPrime := hQ
    haveI : NeZero Q := ⟨hQ0⟩
    exact Nat.absNorm_under_prime Q
  let qZ : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have hQl : Q.LiesOver qZ := by
    simpa [q, qZ] using (inferInstance : Q.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ Q) : ℤ)} : Set ℤ)))
  have hnorm : Ideal.absNorm Q = q ^ (qZ.inertiaDeg' Q) := by
    exact Ideal.absNorm_eq_pow_inertiaDeg' (R := NumberField.RingOfIntegers K) Q hq
  have hnot_dvd : ¬ p ∣ Ideal.absNorm Q := by
    intro hpdvd
    have hpdvd_pow : p ∣ q ^ (qZ.inertiaDeg' Q) := by
      simpa [hnorm] using hpdvd
    have hqp : q = p := by
      have hp_dvd_q : p ∣ q := Nat.Prime.dvd_of_dvd_pow hp hpdvd_pow
      exact (hq.dvd_iff_eq hp.ne_one).mp hp_dvd_q
    have hQp : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
      simpa [qZ, hqp] using hQl
    exact hnot hQp
  rw [Nat.factorization_pow]
  have hfac_zero : (Ideal.absNorm Q).factorization p = 0 := by
    exact Nat.factorization_eq_zero_of_not_dvd hnot_dvd
  simp [hfac_zero]

lemma factorization_idealToTuple_entry (I : (Ideal (NumberField.RingOfIntegers K))⁰) {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hPfac : P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) :
    (idealToTuple I (primeIndex (K := K) P hP hP0)).factorization (Ideal.absNorm (Ideal.under ℤ P)) =
      (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)).inertiaDeg' P *
        (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))).count P := by
  classical
  let J : Ideal (NumberField.RingOfIntegers K) := I
  have hJ : J ≠ ⊥ := by
    dsimp [J]
    simpa using (nonZeroDivisors.coe_ne_zero I)
  let fac : Multiset (Ideal (NumberField.RingOfIntegers K)) := UniqueFactorizationMonoid.normalizedFactors J
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let idx : Fin (Module.finrank ℚ K) := primeIndex (K := K) P hP hP0
  have hp : Nat.Prime p := by
    dsimp [p]
    haveI : P.IsPrime := hP
    haveI : NeZero P := ⟨hP0⟩
    exact Nat.absNorm_under_prime P
  have hPl : P.LiesOver pZ := by
    simpa [p, pZ] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))
  have hPmem : P ∈ fac.toFinset := by
    dsimp [fac, J]
    exact Multiset.mem_toFinset.mpr hPfac
  let T := {Q : Ideal (NumberField.RingOfIntegers K) // Q ∈ fac.toFinset}
  have hQfac_of : ∀ Q : T, Q.1 ∈ fac := fun Q => Multiset.mem_toFinset.mp Q.2
  have hQprime_of : ∀ Q : T, Q.1.IsPrime := fun Q =>
    ((Ideal.mem_normalizedFactors_iff hJ).mp (hQfac_of Q)).1
  have hQ0_of : ∀ Q : T, Q.1 ≠ ⊥ := by
    intro Q hbot
    have hJle : J ≤ ⊥ := by
      simpa [hbot] using ((Ideal.mem_normalizedFactors_iff hJ).mp (hQfac_of Q)).2
    exact hJ (le_bot_iff.mp hJle)
  let g : T → ℕ := fun Q =>
    if primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx then
      Ideal.absNorm Q.1 ^ fac.count Q.1 else 1
  have hg_ne : ∀ Q ∈ (Finset.univ : Finset T), g Q ≠ 0 := by
    intro Q hQ
    dsimp [g]
    by_cases h : primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx
    · rw [if_pos h]
      exact pow_ne_zero _ (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero (hQ0_of Q)))
    · rw [if_neg h]
      exact one_ne_zero
  have hprod_fac : (∏ Q : T, g Q).factorization = ∑ Q : T, (g Q).factorization := by
    exact Nat.factorization_prod (S := (Finset.univ : Finset T)) (g := g) hg_ne
  have hprod_eval : (∏ Q : T, g Q).factorization p = ∑ Q : T, (g Q).factorization p := by
    rw [hprod_fac, Finsupp.finset_sum_apply]
  have hterm_P : (g (⟨P, hPmem⟩ : T)).factorization p = pZ.inertiaDeg' P * fac.count P := by
    dsimp [g]
    have hpr : primeIndex (K := K) P hP hP0 = idx := rfl
    rw [if_pos hpr]
    simpa [p, pZ] using absNorm_pow_factorization_eq P hP hP0 (fac.count P)
  have hterm_other : ∀ Q : T, Q ≠ (⟨P, hPmem⟩ : T) → (g Q).factorization p = 0 := by
    intro Q hQne
    dsimp [g]
    by_cases h : primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx
    · rw [if_pos h]
      have hnot_lie : ¬ Q.1.LiesOver pZ := by
        intro hlie
        have h_eq := primeIndex_inj_of_liesOver (K := K) hP hP0 (hQprime_of Q) (hQ0_of Q) hp hPl hlie
            (by simpa [idx] using h.symm)
        have hsub : Q = (⟨P, hPmem⟩ : T) := Subtype.ext h_eq.symm
        exact hQne hsub
      exact absNorm_pow_factorization_eq_zero_of_not_liesOver (hQprime_of Q) (hQ0_of Q) hp hnot_lie (fac.count Q.1)
    · rw [if_neg h]
      simp
  have hsum_eq : (∑ Q : T, (g Q).factorization p) = pZ.inertiaDeg' P * fac.count P := by
    rw [Finset.sum_eq_single (⟨P, hPmem⟩ : T)]
    · exact hterm_P
    · intro b hb hne
      exact hterm_other b hne
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  have hmain : (idealToTuple I idx).factorization p = pZ.inertiaDeg' P * fac.count P := by
    dsimp [idealToTuple, J, fac]
    change (∏ Q : T, g Q).factorization p = pZ.inertiaDeg' P * fac.count P
    rw [hprod_eval, hsum_eq]
  simpa [p, pZ, idx, fac, J] using hmain

lemma factorization_idealToTuple_entry_eq_zero_of_not_mem (J : (Ideal (NumberField.RingOfIntegers K))⁰) {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hPnot : P ∉ (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))).toFinset) :
    (idealToTuple J (primeIndex (K := K) P hP hP0)).factorization (Ideal.absNorm (Ideal.under ℤ P)) = 0 := by
  classical
  let I0 : Ideal (NumberField.RingOfIntegers K) := J
  have hI0 : I0 ≠ ⊥ := by
    dsimp [I0]
    simpa using (nonZeroDivisors.coe_ne_zero J)
  let fac : Multiset (Ideal (NumberField.RingOfIntegers K)) := UniqueFactorizationMonoid.normalizedFactors I0
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let idx : Fin (Module.finrank ℚ K) := primeIndex (K := K) P hP hP0
  have hp : Nat.Prime p := by
    dsimp [p]
    haveI : P.IsPrime := hP
    haveI : NeZero P := ⟨hP0⟩
    exact Nat.absNorm_under_prime P
  have hPl : P.LiesOver pZ := by
    simpa [p, pZ] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))
  have hPnot_fac : P ∉ fac.toFinset := by
    simpa [fac, I0] using hPnot
  let T := {Q : Ideal (NumberField.RingOfIntegers K) // Q ∈ fac.toFinset}
  have hQfac_of : ∀ Q : T, Q.1 ∈ fac := fun Q => Multiset.mem_toFinset.mp Q.2
  have hQprime_of : ∀ Q : T, Q.1.IsPrime := fun Q =>
    ((Ideal.mem_normalizedFactors_iff hI0).mp (hQfac_of Q)).1
  have hQ0_of : ∀ Q : T, Q.1 ≠ ⊥ := by
    intro Q hbot
    have hI0le : I0 ≤ ⊥ := by
      simpa [hbot] using ((Ideal.mem_normalizedFactors_iff hI0).mp (hQfac_of Q)).2
    exact hI0 (le_bot_iff.mp hI0le)
  let g : T → ℕ := fun Q =>
    if primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx then
      Ideal.absNorm Q.1 ^ fac.count Q.1 else 1
  have hg_ne : ∀ Q ∈ (Finset.univ : Finset T), g Q ≠ 0 := by
    intro Q hQ
    dsimp [g]
    by_cases h : primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx
    · rw [if_pos h]
      exact pow_ne_zero _ (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero (hQ0_of Q)))
    · rw [if_neg h]
      exact one_ne_zero
  have hprod_fac : (∏ Q : T, g Q).factorization = ∑ Q : T, (g Q).factorization := by
    exact Nat.factorization_prod (S := (Finset.univ : Finset T)) (g := g) hg_ne
  have hprod_eval : (∏ Q : T, g Q).factorization p = ∑ Q : T, (g Q).factorization p := by
    rw [hprod_fac, Finsupp.finset_sum_apply]
  have hterm_other : ∀ Q : T, (g Q).factorization p = 0 := by
    intro Q
    dsimp [g]
    by_cases h : primeIndex (K := K) Q.1 (hQprime_of Q) (hQ0_of Q) = idx
    · rw [if_pos h]
      have hnot_lie : ¬ Q.1.LiesOver pZ := by
        intro hlie
        have h_eq := primeIndex_inj_of_liesOver (K := K) hP hP0 (hQprime_of Q) (hQ0_of Q) hp hPl hlie
            (by simpa [idx] using h.symm)
        have hPQ : P = Q.1 := h_eq
        have hPmem : P ∈ fac.toFinset := by
          rw [hPQ]
          exact Q.2
        exact hPnot_fac hPmem
      exact absNorm_pow_factorization_eq_zero_of_not_liesOver (hQprime_of Q) (hQ0_of Q) hp hnot_lie (fac.count Q.1)
    · rw [if_neg h]
      simp
  have hsum_zero : (∑ Q : T, (g Q).factorization p) = 0 := by
    exact Finset.sum_eq_zero (fun Q hQ => hterm_other Q)
  have hmain : (idealToTuple J idx).factorization p = 0 := by
    dsimp [idealToTuple, I0, fac]
    change (∏ Q : T, g Q).factorization p = 0
    rw [hprod_eval, hsum_zero]
  simpa [p, idx, fac, I0] using hmain

lemma idealToTuple_injective :
    Function.Injective (fun I : (Ideal (NumberField.RingOfIntegers K))⁰ => idealToTuple I) := by
  classical
  intro I J h
  apply Subtype.ext
  have hI_ne : (I : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    simpa using (nonZeroDivisors.coe_ne_zero I)
  have hJ_ne : (J : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    simpa using (nonZeroDivisors.coe_ne_zero J)
  have hfac_eq : UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K)) =
      UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K)) := by
    rw [Multiset.ext]
    intro P
    by_cases hPprime : P.IsPrime
    · by_cases hP0 : P ≠ ⊥
      · let p : ℕ := Ideal.absNorm (Ideal.under ℤ P)
        let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
        let idx : Fin (Module.finrank ℚ K) := primeIndex (K := K) P hPprime hP0
        have hp : Nat.Prime p := by
          dsimp [p]
          haveI : P.IsPrime := hPprime
          haveI : NeZero P := ⟨hP0⟩
          exact Nat.absNorm_under_prime P
        have hPl : P.LiesOver pZ := by
          simpa [p, pZ] using (inferInstance : P.LiesOver (Ideal.span ({(Ideal.absNorm (Ideal.under ℤ P) : ℤ)} : Set ℤ)))
        have hf_pos : 0 < pZ.inertiaDeg' P := by
          haveI : P.IsPrime := hPprime
          haveI : P.LiesOver pZ := hPl
          exact Ideal.inertiaDeg'_pos' pZ P
        have h_entry : idealToTuple I idx = idealToTuple J idx := by
          exact congrFun h idx
        have hval_eq : (idealToTuple I idx).factorization p = (idealToTuple J idx).factorization p := by
          rw [h_entry]
        -- show counts equal by cases on membership
        by_cases hPfacI : P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))
        · have hPmemI : P ∈ (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))).toFinset :=
            Multiset.mem_toFinset.mpr hPfacI
          have hvalI := factorization_idealToTuple_entry I hPprime hP0 hPfacI
          have hcountI_pos : 0 < Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) :=
            Multiset.count_pos.mpr hPfacI
          have hPfacJ : P ∈ UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K)) := by
            by_contra hnot
            have hPnotJ : P ∉ (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))).toFinset :=
              Multiset.mem_toFinset.not.mpr hnot
            have hvalJ0 := factorization_idealToTuple_entry_eq_zero_of_not_mem J hPprime hP0 hPnotJ
            have hvalI' : (idealToTuple I idx).factorization p = pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) := by
              simpa [p, pZ, idx] using hvalI
            have hvalJ' : (idealToTuple J idx).factorization p = 0 := by
              simpa [p, pZ, idx] using hvalJ0
            have hnonzero : pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) ≠ 0 := by
              exact Nat.mul_ne_zero (Nat.ne_of_gt hf_pos) (Nat.ne_of_gt hcountI_pos)
            exact hnonzero (by rw [← hvalI', hval_eq, hvalJ'])
          have hvalJ := factorization_idealToTuple_entry J hPprime hP0 hPfacJ
          have hvalI' : (idealToTuple I idx).factorization p = pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) := by
            simpa [p, pZ, idx] using hvalI
          have hvalJ' : (idealToTuple J idx).factorization p = pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))) := by
            simpa [p, pZ, idx] using hvalJ
          have hmul : pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))) =
              pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))) := by
            rw [← hvalI', hval_eq, hvalJ']
          exact Nat.mul_left_cancel hf_pos hmul
        · have hPfacI_not : P ∉ (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))).toFinset :=
            Multiset.mem_toFinset.not.mpr hPfacI
          have hvalI0 := factorization_idealToTuple_entry_eq_zero_of_not_mem I hPprime hP0 hPfacI_not
          by_cases hPfacJ : P ∈ UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))
          · have hPmemJ : P ∈ (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))).toFinset :=
              Multiset.mem_toFinset.mpr hPfacJ
            have hvalJ := factorization_idealToTuple_entry J hPprime hP0 hPfacJ
            have hcountJ_pos : 0 < Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))) :=
              Multiset.count_pos.mpr hPfacJ
            have hvalI' : (idealToTuple I idx).factorization p = 0 := by
              simpa [p, pZ, idx] using hvalI0
            have hvalJ' : (idealToTuple J idx).factorization p = pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))) := by
              simpa [p, pZ, idx] using hvalJ
            have hnonzero : pZ.inertiaDeg' P * Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))) ≠ 0 := by
              exact Nat.mul_ne_zero (Nat.ne_of_gt hf_pos) (Nat.ne_of_gt hcountJ_pos)
            exfalso
            exact hnonzero (by rw [← hvalJ', ← hval_eq, hvalI'])
          · rw [Multiset.count_eq_zero.mpr hPfacI, Multiset.count_eq_zero.mpr hPfacJ]
      · -- P = ⊥, count zero for both
        have hPbot : P = ⊥ := by simpa using hP0
        subst P
        have hI_bot_not : (⊥ : Ideal (NumberField.RingOfIntegers K)) ∉ UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K)) := by
          intro hmem
          exact hI_ne (le_bot_iff.mp ((Ideal.mem_normalizedFactors_iff hI_ne).mp hmem).2)
        have hJ_bot_not : (⊥ : Ideal (NumberField.RingOfIntegers K)) ∉ UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K)) := by
          intro hmem
          exact hJ_ne (le_bot_iff.mp ((Ideal.mem_normalizedFactors_iff hJ_ne).mp hmem).2)
        rw [Multiset.count_eq_zero.mpr hI_bot_not, Multiset.count_eq_zero.mpr hJ_bot_not]
    · -- P not prime, count zero for both
      have hI_not : P ∉ UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K)) := by
        intro hmem
        exact hPprime ((Ideal.mem_normalizedFactors_iff hI_ne).mp hmem).1
      have hJ_not : P ∉ UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K)) := by
        intro hmem
        exact hPprime ((Ideal.mem_normalizedFactors_iff hJ_ne).mp hmem).1
      rw [Multiset.count_eq_zero.mpr hI_not, Multiset.count_eq_zero.mpr hJ_not]
  have hI_eq : (I : Ideal (NumberField.RingOfIntegers K)) = (J : Ideal (NumberField.RingOfIntegers K)) := by
    calc
      (I : Ideal (NumberField.RingOfIntegers K)) = (UniqueFactorizationMonoid.normalizedFactors (I : Ideal (NumberField.RingOfIntegers K))).prod :=
        (Ideal.prod_normalizedFactors_eq_self hI_ne).symm
      _ = (UniqueFactorizationMonoid.normalizedFactors (J : Ideal (NumberField.RingOfIntegers K))).prod := by rw [hfac_eq]
      _ = (J : Ideal (NumberField.RingOfIntegers K)) := Ideal.prod_normalizedFactors_eq_self hJ_ne
  exact hI_eq

theorem ideal_card_norm_le_tupleFinset (K : Type*) [Field K] [NumberField K] (A : ℕ) :
    Nat.card {I : (Ideal (NumberField.RingOfIntegers K))⁰ //
      Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ A} ≤
      (Commons.NumberTheory.Nat.tupleFinset (Module.finrank ℚ K) A).card := by
  classical
  let S := {I : (Ideal (NumberField.RingOfIntegers K))⁰ // Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ A}
  let f : S → Fin (Module.finrank ℚ K) → ℕ := fun I => idealToTuple I.1
  have hf_inj : Function.Injective f := by
    intro I J h
    apply Subtype.ext
    exact idealToTuple_injective h
  have hfinS : {I : (Ideal (NumberField.RingOfIntegers K))⁰ | Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ A}.Finite := by
    exact Ideal.finite_setOfPred_absNorm_le₀ A
  haveI : Fintype S := by
    dsimp [S]
    exact hfinS.fintype
  have hcard_image : (Finset.univ.image f).card = Fintype.card S := by
    rw [Finset.card_image_of_injective (s := (Finset.univ : Finset S)) hf_inj]
    simp
  have hsub : Finset.univ.image f ⊆ Commons.NumberTheory.Nat.tupleFinset (Module.finrank ℚ K) A := by
    rw [Finset.image_subset_iff]
    intro I hI
    exact idealToTuple_mem_tupleFinset A I
  have hle_fintype : Fintype.card S ≤ (Commons.NumberTheory.Nat.tupleFinset (Module.finrank ℚ K) A).card := by
    rw [← hcard_image]
    exact Finset.card_le_card hsub
  simpa [S] using hle_fintype


end Commons.NumberTheory.NumberField
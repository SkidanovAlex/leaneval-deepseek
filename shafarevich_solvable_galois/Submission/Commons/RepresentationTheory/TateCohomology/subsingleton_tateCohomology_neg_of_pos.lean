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
import Submission.Commons.RepresentationTheory.GroupCohomology.subsingleton_groupCohomology_coind_bot_restrict
import Submission.Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-
# Vanishing of negative Tate cohomology from the vanishing of `H¹` and `H²`

This file proves that if a `ℤ`-linear representation `A` of a finite group `G` satisfies
`H¹(H, A) = 0 = H²(H, A)` for every subgroup `H ≤ G`, and if moreover the positive-degree
Tate cohomology of every such representation (for every finite group) vanishes, then the Tate
cohomology of `A` vanishes in every *negative* degree as well.

The argument is the standard dimension-shifting argument for cohomologically trivial modules.
For any representation `B` we construct a short exact sequence
`0 ⟶ D ⟶ M ⟶ B ⟶ 0`
where `M = Coind_⊥^G(B.V)` is the coindution of the trivial representation on the underlying
`ℤ`-module of `B` from the trivial subgroup.  The module `M` is acyclic: its Tate cohomology
vanishes in every degree, and this remains true after restriction to any subgroup.  Hence the
connecting homomorphism gives isomorphisms `Ĥʳ(G, B) ≅ Ĥʳ⁺¹(G, D)` in every degree, and likewise
for every subgroup.  In particular `Ĥ⁰(G, D)` agrees with `Ĥ⁻¹(G, B)`, so the positive-degree
vanishing hypothesis applied to `D` produces the vanishing in degree `-1`, and iterating the
construction produces the vanishing in all negative degrees.

## Main result

* `subsingleton_tateCohomology_neg_of_pos`
-/

open CategoryTheory

namespace Commons.RepresentationTheory.TateCohomology

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

-- Allows `Fintype ↥H` to be found by typeclass search for subgroups of a finite group.
attribute [local instance] Classical.propDecidable

variable {G : Type} [Group G] [Fintype G]

/-! ## The acyclic middle term and a surjection onto a given representation -/

section Middle

variable (B : Rep ℤ G)

noncomputable local instance : Module ℤ B.V := B.hV2

/-- The trivial representation of `⊥ ≤ G` on the underlying `ℤ`-module of `B`. -/
noncomputable abbrev coindCoeff : Rep ℤ (⊥ : Subgroup G) :=
  Rep.trivial ℤ (⊥ : Subgroup G) B.V

/-- The coinduction of the trivial representation on `B.V` from the trivial subgroup.  It is
acyclic in every degree for `G` and stays acyclic after restriction to any subgroup. -/
noncomputable abbrev coindMid : Rep ℤ G :=
  Rep.coind (⊥ : Subgroup G).subtype (coindCoeff B)

noncomputable local instance : Module ℤ (coindMid B).V := (coindMid B).hV2

/-- The `x`-th coordinate functional `coindMid B → B`. -/
noncomputable def projFun (x : G) : coindMid B →ₗ[ℤ] B :=
  (LinearMap.proj x).comp
    (Submodule.subtype (Representation.coindV (⊥ : Subgroup G).subtype (coindCoeff B).ρ))

/-- The `G`-equivariant map `coindMid B → B`, `f ↦ ∑ x, ρ(x⁻¹) (f x)`. -/
noncomputable def linMap : coindMid B →ₗ[ℤ] B :=
  ∑ x : G, (B.ρ x⁻¹).comp (projFun B x)

lemma linMap_apply (f : coindMid B) : linMap B f = ∑ x : G, B.ρ x⁻¹ (f.1 x) := by
  simp only [linMap, LinearMap.sum_apply, LinearMap.comp_apply, projFun, LinearMap.proj_apply,
    Submodule.subtype_apply]

lemma coindMid_ρ_apply (h : G) (f : coindMid B) (x : G) :
    (((coindMid B).ρ h) f).1 x = f.1 (x * h) := rfl

theorem linMap_intertwines (h : G) :
    linMap B ∘ₗ (coindMid B).ρ h = (B.ρ h) ∘ₗ linMap B := by
  ext f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, linMap_apply, linMap_apply, map_sum]
  refine Fintype.sum_bijective (· * h) (Group.mulRight_bijective h) _ _ (fun x => ?_)
  rw [coindMid_ρ_apply, ← Module.End.mul_apply, ← map_mul]
  congr 1
  group

theorem linMap_surjective : Function.Surjective (linMap B) := by
  classical
  intro b
  have hm : Pi.single 1 b ∈ Representation.coindV (⊥ : Subgroup G).subtype (coindCoeff B).ρ := by
    rw [Representation.mem_coindV]
    intro g h
    have hg' : g = 1 := Subtype.ext (Subgroup.mem_bot.mp g.2)
    rw [hg']
    simp
  refine ⟨⟨Pi.single 1 b, hm⟩, ?_⟩
  rw [linMap_apply]
  have hcoe : (↑(⟨Pi.single 1 b, hm⟩ : (coindMid B).V) : G → B.V) = Pi.single 1 b := rfl
  rw [hcoe]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro x _ hx
    rw [Pi.single_eq_of_ne hx, map_zero]
  · intro h
    exact absurd (Finset.mem_univ 1) h

/-- The canonical surjection from the acyclic middle term onto `B`. -/
noncomputable def coindEpi : coindMid B ⟶ B :=
  Rep.ofHom ⟨linMap B, linMap_intertwines B⟩

theorem coindEpi_surjective : Function.Surjective (coindEpi B) := fun b =>
  let ⟨f, hf⟩ := linMap_surjective B b
  ⟨f, hf⟩

theorem coindEpi_epi : Epi (coindEpi B) :=
  (Rep.epi_iff_surjective _).2 (coindEpi_surjective B)

end Middle

/-! ## Acyclicity of the restricted coinduced module -/

/-- The coinduction of a trivial representation from the trivial subgroup has vanishing Tate
cohomology in every degree; moreover this remains true after restricting to a subgroup. -/
theorem subsingleton_tateCohomology_coind_bot_restrict_all (H : Subgroup G)
    (W : Rep ℤ (⊥ : Subgroup G)) (r : ℤ) :
    Subsingleton (tateCohomology (Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype W)) r) := by
  let C : Rep ℤ (⊥ : Subgroup H) :=
    Commons.RepresentationTheory.GroupCohomology.supersingletonCoindCoeff H W
  haveI : Subsingleton (tateCohomology (Rep.coind (⊥ : Subgroup H).subtype C) r) :=
    Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot C r
  have hIso : Nonempty (Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype W) ≅
      Rep.coind (⊥ : Subgroup H).subtype C) := by
    letI : Module ℤ (Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype W)).V :=
      (Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype W)).hV2
    letI : Module ℤ (Rep.coind (⊥ : Subgroup H).subtype C).V :=
      (Rep.coind (⊥ : Subgroup H).subtype C).hV2
    exact ⟨Rep.mkIso (Representation.Equiv.mk
      (Commons.RepresentationTheory.GroupCohomology.supersingletonResCoindBotLinearEquiv H W)
      (fun s => LinearMap.ext (fun f =>
        Commons.RepresentationTheory.GroupCohomology.supersingletonResCoindBotLinearEquiv_equivariant
          H W s f)))⟩
  obtain ⟨e⟩ := hIso
  exact (Functor.mapIso (tateCohomologyFunctor (R := ℤ) (G := H) r) e).toLinearEquiv.injective.subsingleton

/-! ## The short exact sequence, its acyclicity, and the dimension shifts -/

/-- **Dimension shifting.** If `S : X₁ ⟶ X₂ ⟶ X₃` is a short exact sequence of `ℤ[G]`-modules
whose middle term is trivial in degrees `r` and `r + 1`, then the connecting homomorphism gives an
isomorphism `Ĥʳ(G, X₃) ≅ Ĥʳ⁺¹(G, X₁)`. -/
theorem tateCohomology_iso_of_acyclic_middle_of_subsingleton
    (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact) (r : ℤ)
    (h₁ : Subsingleton (tateCohomology S.X₂ r))
    (h₂ : Subsingleton (tateCohomology S.X₂ (r + 1))) :
    Nonempty (tateCohomology S.X₃ r ≃ₗ[ℤ] tateCohomology S.X₁ (r + 1)) := by
  haveI hz₁ : Subsingleton ↥((S.map (tateComplexFunctor ℤ G)).X₂.homology r) := h₁
  haveI hz₂ : Subsingleton ↥((S.map (tateComplexFunctor ℤ G)).X₂.homology (r + 1)) := h₂
  haveI : IsIso (TateCohomology.δ hS r) :=
    ShortComplex.ShortExact.isIso_δ (TateCohomology.map_tateComplexFunctor_shortExact hS) r (r + 1)
      rfl (ModuleCat.isZero_of_subsingleton _) (ModuleCat.isZero_of_subsingleton _)
  exact ⟨(asIso (TateCohomology.δ hS r)).toLinearEquiv⟩

section ShortComplexPart

variable (B : Rep ℤ G)

/-- The short exact sequence `0 → D → coindMid B → B → 0` with acyclic middle term. -/
noncomputable def acyclicShortComplex : ShortComplex (Rep ℤ G) :=
  ShortComplex.kernelSequence (coindEpi B)

lemma acyclicShortComplex_X₂ : (acyclicShortComplex B).X₂ = coindMid B := rfl

theorem acyclicShortComplex_shortExact : (acyclicShortComplex B).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact (coindEpi B))
    (inferInstance : Mono (ShortComplex.kernelSequence (coindEpi B)).f)
    (coindEpi_epi B)

theorem acyclicShortComplex_acyclic_middle_G (r : ℤ) :
    Subsingleton (tateCohomology (acyclicShortComplex B).X₂ r) :=
  Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot
    (coindCoeff B) r

theorem acyclicShortComplex_acyclic_middle_restrict_all (H : Subgroup G) (r : ℤ) :
    Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₂) r) :=
  Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot_restrict_all
    H (coindCoeff B) r

/-- Dimension shift: `Ĥʳ(G, B) ≅ Ĥʳ⁺¹(G, D)` where `D` is the kernel term. -/
theorem acyclicShortComplex_shift_up (r : ℤ) :
    Nonempty (tateCohomology (acyclicShortComplex B).X₃ r ≃ₗ[ℤ]
      tateCohomology (acyclicShortComplex B).X₁ (r + 1)) :=
  tateCohomology_iso_of_acyclic_middle_of_subsingleton (acyclicShortComplex B)
    (acyclicShortComplex_shortExact B) r (acyclicShortComplex_acyclic_middle_G B r)
    (acyclicShortComplex_acyclic_middle_G B (r + 1))

/-- Dimension shift, in the form used to show that the kernel term inherits the
vanishing hypothesis. -/
theorem acyclicShortComplex_shift_down (r : ℤ) :
    Nonempty (tateCohomology (acyclicShortComplex B).X₁ r ≃ₗ[ℤ]
      tateCohomology (acyclicShortComplex B).X₃ (r - 1)) := by
  obtain ⟨e⟩ := acyclicShortComplex_shift_up B (r - 1)
  rw [show (r - 1) + 1 = r from by omega] at e
  exact ⟨e.symm⟩

/-- Dimension shift at the level of an arbitrary subgroup. -/
theorem acyclicShortComplex_shift_restrict_up (H : Subgroup G) (r : ℤ) :
    Nonempty (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) r ≃ₗ[ℤ]
      tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) (r + 1)) := by
  have hS : ((acyclicShortComplex B).map (Rep.resFunctor H.subtype)).ShortExact :=
    (Rep.shortExact_res (k := ℤ) H.subtype).2 (acyclicShortComplex_shortExact B)
  obtain ⟨e⟩ := tateCohomology_iso_of_acyclic_middle_of_subsingleton
    ((acyclicShortComplex B).map (Rep.resFunctor H.subtype)) hS r
    (acyclicShortComplex_acyclic_middle_restrict_all B H r)
    (acyclicShortComplex_acyclic_middle_restrict_all B H (r + 1))
  exact ⟨e⟩

/-- Dimension shift at the level of an arbitrary subgroup, in the form used to show that the
kernel term inherits the vanishing hypothesis. -/
theorem acyclicShortComplex_shift_restrict_down (H : Subgroup G) (r : ℤ) :
    Nonempty (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) r ≃ₗ[ℤ]
      tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) (r - 1)) := by
  obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H (r - 1)
  rw [show (r - 1) + 1 = r from by omega] at e
  exact ⟨e.symm⟩

end ShortComplexPart

/-! ## Comparing restrictions along subgroups -/

/-- Restricting a representation first to `H` and then to a subgroup `H' ≤ H` is the same as
restricting along the canonical isomorphism `H' ≅ H'.map H.subtype`. -/
theorem groupCohomology_res_res_iso (H : Subgroup G) (H' : Subgroup H) (B : Rep ℤ G) (n : ℕ) :
    Nonempty (groupCohomology (Rep.res H'.subtype (Rep.res H.subtype B)) n ≅
      groupCohomology (Rep.res (H'.map H.subtype).subtype B) n) := by
  letI : Module ℤ B.V := B.hV2
  let e : H' ≃* H'.map H.subtype :=
    Subgroup.equivMapOfInjective H' H.subtype H.subtype_injective
  refine ⟨groupCohomology.mapIso e (LinearEquiv.refl ℤ B.V) ?_ n⟩
  intro x
  ext v
  rfl

/-! ## The vanishing hypothesis and the kernel construction -/

/-- `B` has vanishing Tate cohomology in all nonnegative degrees after restriction to every
subgroup. -/
def PosTateVanishing (B : Rep ℤ G) : Prop :=
  ∀ (H : Subgroup G) (r : ℤ), 0 ≤ r → Subsingleton (tateCohomology (Rep.res H.subtype B) r)

/-- Vanishing of the kernel term in degree `1`. -/
theorem subsingleton_tateCohomology_kernel_one {B : Rep ℤ G} (hB : PosTateVanishing B)
    (H : Subgroup G) :
    Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 1) := by
  obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H 0
  haveI : Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) 0) :=
    hB H 0 le_rfl
  rw [show (0 : ℤ) + 1 = 1 from by norm_num] at e
  exact e.symm.injective.subsingleton

/-- Vanishing of the kernel term in degree `2`. -/
theorem subsingleton_tateCohomology_kernel_two {B : Rep ℤ G} (hB : PosTateVanishing B)
    (H : Subgroup G) :
    Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 2) := by
  obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H 1
  haveI : Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) 1) :=
    hB H 1 (by norm_num)
  rw [show (1 : ℤ) + 1 = 2 from by norm_num] at e
  exact e.symm.injective.subsingleton

/-- The kernel term satisfies the `H¹`/`H²` hypothesis of `hpos`. -/
theorem subsingleton_groupCohomology_kernel_one_two {B : Rep ℤ G} (hB : PosTateVanishing B)
    (H : Subgroup G) :
    Subsingleton (groupCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 1) ∧
      Subsingleton (groupCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 2) := by
  constructor
  · haveI := subsingleton_tateCohomology_kernel_one hB H
    exact (TateCohomology.isoGroupCohomology (R := ℤ) (G := H) 1).app _ |>.symm.toLinearEquiv.injective.subsingleton
  · haveI := subsingleton_tateCohomology_kernel_two hB H
    exact (TateCohomology.isoGroupCohomology (R := ℤ) (G := H) 2).app _ |>.symm.toLinearEquiv.injective.subsingleton

/-- The kernel term of the acyclic short exact sequence inherits the vanishing hypothesis, once
the vanishing in degree `-1` is known. -/
theorem posTateVanishing_kernel {B : Rep ℤ G} (hB : PosTateVanishing B)
    (hneg : ∀ H : Subgroup G, Subsingleton (tateCohomology (Rep.res H.subtype B) (-1))) :
    PosTateVanishing (acyclicShortComplex B).X₁ := by
  intro H r hr
  obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_down B H r
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · subst hr0
    haveI : Subsingleton
        (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) (0 - 1 : ℤ)) := by
      rw [show (0 : ℤ) - 1 = -1 from by norm_num]
      exact hneg H
    exact e.injective.subsingleton
  · haveI : Subsingleton
        (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) (r - 1)) :=
      hB H (r - 1) (by omega)
    exact e.injective.subsingleton

/-! ## The dimension-shifting induction -/

/-- **Main induction.** If the Tate cohomology of `B` vanishes in all nonnegative degrees after
restriction to every subgroup of `G`, then it vanishes in all negative degrees, both for `G` and
for all of its subgroups.  The hypothesis `hpos` is the positive-degree vanishing statement used
for the `Ĥ⁰` of the kernel term. -/
theorem subsingleton_tateCohomology_neg_of_posTateVanishing {G : Type} [Group G] [Fintype G]
    (hpos : ∀ (K : Type) [Group K] [Fintype K] (B : Rep ℤ K),
        (∀ H : Subgroup K, Subsingleton (groupCohomology (Rep.res H.subtype B) 1) ∧
          Subsingleton (groupCohomology (Rep.res H.subtype B) 2)) →
        ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology B r))
    (B : Rep ℤ G) (hB : PosTateVanishing B) : ∀ r : ℤ, r < 0 → Subsingleton (tateCohomology B r) := by
  have main : ∀ n : ℕ, 1 ≤ n → ∀ (B : Rep ℤ G), PosTateVanishing B →
      Subsingleton (tateCohomology B (-(n : ℤ))) ∧
        ∀ H : Subgroup G,
          Subsingleton (tateCohomology (Rep.res H.subtype B) (-(n : ℤ))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn B hB
      rcases (by omega : n = 1 ∨ 2 ≤ n) with hn1 | hn2
      · subst hn1
        constructor
        · -- `Ĥ⁻¹(G, B) ≅ Ĥ⁰(G, D)` and `Ĥ⁰(G, D) = 0` by `hpos` applied to `D`.
          obtain ⟨e⟩ := acyclicShortComplex_shift_up B (-1)
          rw [show (-1 : ℤ) + 1 = 0 from by norm_num] at e
          haveI : Subsingleton (tateCohomology (acyclicShortComplex B).X₁ 0) :=
            hpos G (acyclicShortComplex B).X₁
              (fun H => subsingleton_groupCohomology_kernel_one_two hB H) 0 le_rfl
          exact e.injective.subsingleton
        · intro H
          obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H (-1)
          rw [show (-1 : ℤ) + 1 = 0 from by norm_num] at e
          haveI : Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 0) :=
            hpos H (Rep.res H.subtype (acyclicShortComplex B).X₁) (fun H' => ?_) 0 le_rfl
          · exact e.injective.subsingleton
          · obtain ⟨e1⟩ := groupCohomology_res_res_iso H H' (acyclicShortComplex B).X₁ 1
            obtain ⟨e2⟩ := groupCohomology_res_res_iso H H' (acyclicShortComplex B).X₁ 2
            obtain ⟨h1, h2⟩ := subsingleton_groupCohomology_kernel_one_two hB (H'.map H.subtype)
            exact ⟨e1.toLinearEquiv.injective.subsingleton,
              e2.toLinearEquiv.injective.subsingleton⟩
      · -- `n ≥ 2`: use the induction hypothesis for the kernel term
        have hneg : ∀ H : Subgroup G,
            Subsingleton (tateCohomology (Rep.res H.subtype B) (-1)) := by
          intro H
          have h1 := (ih 1 (by omega) (by omega) B hB).2 H
          simpa using h1
        have hD : PosTateVanishing (acyclicShortComplex B).X₁ := posTateVanishing_kernel hB hneg
        constructor
        · obtain ⟨e⟩ := acyclicShortComplex_shift_up B (-(n : ℤ))
          rw [show -(n : ℤ) + 1 = -(((n - 1 : ℕ)) : ℤ) from by omega] at e
          haveI : Subsingleton (tateCohomology (acyclicShortComplex B).X₁
              (-((n - 1 : ℕ) : ℤ))) := (ih (n - 1) (by omega) (by omega) _ hD).1
          exact e.injective.subsingleton
        · intro H
          obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H (-(n : ℤ))
          rw [show -(n : ℤ) + 1 = -(((n - 1 : ℕ)) : ℤ) from by omega] at e
          haveI : Subsingleton (tateCohomology
              (Rep.res H.subtype (acyclicShortComplex B).X₁) (-((n - 1 : ℕ) : ℤ))) :=
            (ih (n - 1) (by omega) (by omega) _ hD).2 H
          exact e.injective.subsingleton
  intro r hr
  have hrepr : r = -(((-r).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  rw [hrepr]
  exact (main ((-r).toNat) (by omega) B hB).1

/-! ## Deriving the vanishing hypothesis from `hpos` and `hA` -/

/-- The positive-degree vanishing hypothesis `hpos`, applied to `A` and to all of its restrictions
to subgroups using `hA`, yields `PosTateVanishing A`. -/
theorem posTateVanishing_of_pos {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    (hpos : ∀ (K : Type) [Group K] [Fintype K] (B : Rep ℤ K),
        (∀ H : Subgroup K, Subsingleton (groupCohomology (Rep.res H.subtype B) 1) ∧
          Subsingleton (groupCohomology (Rep.res H.subtype B) 2)) →
        ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology B r))
    (hA : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype A) 1) ∧
        Subsingleton (groupCohomology (Rep.res H.subtype A) 2)) :
    PosTateVanishing A := by
  intro H r hr
  refine hpos H (Rep.res H.subtype A) ?_ r hr
  intro H'
  obtain ⟨e1⟩ := groupCohomology_res_res_iso H H' A 1
  obtain ⟨e2⟩ := groupCohomology_res_res_iso H H' A 2
  obtain ⟨h1, h2⟩ := hA (H'.map H.subtype)
  exact ⟨e1.toLinearEquiv.injective.subsingleton,
    e2.toLinearEquiv.injective.subsingleton⟩

/-! ## The main theorem -/

theorem subsingleton_tateCohomology_neg_of_pos {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    (hpos : ∀ (K : Type) [Group K] [Fintype K] (B : Rep ℤ K),
        (∀ H : Subgroup K, Subsingleton (groupCohomology (Rep.res H.subtype B) 1) ∧
          Subsingleton (groupCohomology (Rep.res H.subtype B) 2)) →
        ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology B r))
    (hA : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype A) 1) ∧
        Subsingleton (groupCohomology (Rep.res H.subtype A) 2)) :
    ∀ r : ℤ, r < 0 → Subsingleton (tateCohomology A r) :=
  subsingleton_tateCohomology_neg_of_posTateVanishing hpos A (posTateVanishing_of_pos A hpos hA)

end Commons.RepresentationTheory.TateCohomology
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
import Submission.NK.CFTLib.ARL.kernelLe_of_auxField_B
import Submission.NK.CFTLib.ARLAlt.Descent
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm_of_normal
import Submission.NK.Existence.ArtinLemma.helpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

/-! ## Auxiliary lemmas for the transfer step of Artin's trick -/



/-- `FracCoprime` is multiplicative. -/
lemma FracCoprime.mul {K : Type} [Field K] [NumberField K] {m : ℕ} {A B : Frac K}
    (hA : FracCoprime m A) (hB : FracCoprime m B) : FracCoprime m (A * B) := by
  intro 𝔭 h𝔭
  rw [Units.val_mul, FractionalIdeal.count_mul K 𝔭 (Units.ne_zero A) (Units.ne_zero B),
    hA 𝔭 h𝔭, hB 𝔭 h𝔭, add_zero]

/-- `FracCoprime` is preserved by integer powers. -/
lemma FracCoprime.zpow {K : Type} [Field K] [NumberField K] {m : ℕ} {A : Frac K} (n : ℤ)
    (hA : FracCoprime m A) : FracCoprime m (A ^ n) := by
  intro 𝔭 h𝔭
  rw [Units.val_zpow_eq_zpow_val, FractionalIdeal.count_zpow, hA 𝔭 h𝔭, mul_zero]

/-- **The `𝔭`-adic exponent of the relative norm of a fractional ideal coprime to `(m)` vanishes
at every prime dividing `(m)`.** -/
lemma count_relNormUnit_eq_zero {K E : Type} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] {m : ℕ} {𝔄 : Frac E}
    (h : FracCoprime (K := E) m 𝔄) (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h𝔭 : (m : 𝓞 K) ∈ 𝔭.asIdeal) :
    FractionalIdeal.count K 𝔭
        ((NK.CFTLib.ARL.relNormUnit (K := K) (L := E) 𝔄 : Frac K) :
          FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rw [show ((NK.CFTLib.ARL.relNormUnit (K := K) (L := E) 𝔄 : Frac K) :
      FractionalIdeal (𝓞 K)⁰ K) = NK.CFTLib.ARL.relNormFI (K := K) (L := E)
        (𝔄 : FractionalIdeal (𝓞 E)⁰ E) from rfl,
    NK.CFTLib.ARL.count_relNormFI, NK.CFTLib.ARL.relNormExp]
  refine Finset.sum_eq_zero fun 𝔮 h𝔮 => ?_
  have h𝔮lies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal :=
    (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := E)).mp h𝔮
  have hm𝔮 : (m : 𝓞 E) ∈ 𝔮.asIdeal := by
    have h1 : (m : 𝓞 K) ∈ 𝔮.asIdeal.under (𝓞 K) := by
      rw [← h𝔮lies.over]; exact h𝔭
    have h2 := (Ideal.mem_under (𝓞 K) 𝔮.asIdeal).mp h1
    rwa [map_natCast] at h2
  rw [h 𝔮 hm𝔮, mul_zero]

/-- **A prime ideal is coprime to a natural number that does not lie in it.** -/
lemma fracCoprime_primeUnit {K : Type} [Field K] [NumberField K] {m : ℕ}
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} (h : (m : 𝓞 K) ∉ 𝔮.asIdeal) :
    FracCoprime m (NK.CFTLib.ARL.primeUnit 𝔮) := by
  classical
  intro 𝔭 h𝔭
  rw [NK.CFTLib.ARL.primeUnit_val, FractionalIdeal.count_maximal]
  rw [if_neg]
  intro hEq
  exact h (hEq ▸ h𝔭)

/-- **A natural number lying in a prime ideal of a number field has a prime divisor dividing the
norm of the ideal.** -/
lemma exists_prime_dvd_absNorm_of_mem {K : Type} [Field K] [NumberField K]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) {M : ℕ} (hM : (M : 𝓞 K) ∈ 𝔭.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ M ∧ p ∣ Ideal.absNorm 𝔭.asIdeal := by
  classical
  refine ⟨Ideal.absNorm (𝔭.asIdeal.under ℤ), Nat.absNorm_under_prime 𝔭.asIdeal, ?_, ?_⟩
  · have h1 : (M : ℤ) ∈ Ideal.span {((Ideal.absNorm (𝔭.asIdeal.under ℤ) : ℕ) : ℤ)} := by
      rw [Int.ideal_span_absNorm_eq_self]
      exact (Ideal.mem_under ℤ 𝔭.asIdeal).mpr (by simpa using hM)
    exact Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp h1)
  · exact Int.absNorm_under_dvd_absNorm 𝔭.asIdeal

/-- **`IsUnramified` and `ramificationIdxIn = 1` agree** for a finite Galois extension. -/
theorem isUnramified_iff_ramificationIdxIn_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : NK.Chebotarev.PrimeIdeal K) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p ↔
      p.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
  classical
  letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
  constructor
  · intro hunr
    obtain ⟨Q, hQ⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) p
    haveI : Q.asIdeal.IsPrime := Q.isPrime
    haveI : Q.asIdeal.LiesOver p.asIdeal := hQ
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal Q.asIdeal (Gal(L/K))]
    exact hunr Q hQ
  · intro h Q hQ
    haveI : Q.asIdeal.IsPrime := Q.isPrime
    haveI : Q.asIdeal.LiesOver p.asIdeal := hQ
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal Q.asIdeal (Gal(L/K))]
    exact h

/-- **Descent of unramifiedness to an intermediate field.** -/
theorem isUnramified_intermediateField {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (M : IntermediateField K Ω) [FiniteDimensional K M]
    {p : NK.Chebotarev.PrimeIdeal K}
    (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) = 1) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥M) p := by
  intro P hP
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : P.asIdeal.LiesOver p.asIdeal := hP
  obtain ⟨Q, hQ⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := ↥M) (L := Ω) P
  haveI : Q.asIdeal.IsPrime := Q.isPrime
  haveI : Q.asIdeal.LiesOver P.asIdeal := hQ
  haveI hQp : Q.asIdeal.LiesOver p.asIdeal :=
    Ideal.LiesOver.trans (𝔓 := Q.asIdeal) (P := P.asIdeal) (p := p.asIdeal)
  have hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := Ω) p :=
    (isUnramified_iff_ramificationIdxIn_eq_one (K := K) (L := Ω) p).mpr h
  have hQunr : Q.asIdeal.ramificationIdx (𝓞 K) = 1 := hunr Q hQp
  have hmul : Q.asIdeal.ramificationIdx (𝓞 K)
      = P.asIdeal.ramificationIdx (𝓞 K) * Q.asIdeal.ramificationIdx (𝓞 ↥M) :=
    Ideal.ramificationIdx_tower (q := P.asIdeal) (r := Q.asIdeal)
  rw [hQunr] at hmul
  exact Nat.eq_one_of_mul_eq_one_right hmul.symm

/-- **`count` determines a nonzero fractional ideal.** -/
theorem fractionalIdeal_eq_of_count_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K v I = FractionalIdeal.count K v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

/-- The exponent-vector factorisation of a unit of the group of fractional ideals. -/
theorem frac_eq_finsupp_prod {K : Type*} [Field K] [NumberField K] (A : Frac K) :
    A = (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).prod
        (fun 𝔭 e => (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^ e) := by
  have hcoe : (((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).prod
        (fun 𝔭 e => (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^ e) : Frac K) :
          FractionalIdeal (𝓞 K)⁰ K)
      = (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).prod
          (fun 𝔭 e => (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ e) := by
    rw [Finsupp.prod, Finsupp.prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun 𝔭 _ => ?_
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  have hne : (((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).prod
        (fun 𝔭 e => (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^ e) : Frac K) :
          FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [hcoe, Finsupp.prod]
    refine Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => zpow_ne_zero _ ?_
    exact FractionalIdeal.coeIdeal_ne_zero.mpr 𝔭.ne_bot
  refine Units.ext (fractionalIdeal_eq_of_count_eq K (Units.ne_zero A) hne ?_)
  intro v
  rw [hcoe, FractionalIdeal.count_finsuppProd, NK.CFTLib.Arl.exps_apply]

/-- A product of integer powers of a fixed element of a commutative group is the power by the
sum of the exponents. -/
theorem finset_prod_zpow {ι G : Type*} [CommGroup G] (s : Finset ι) (g : G) (f : ι → ℤ) :
    ∏ i ∈ s, g ^ (f i) = g ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, zpow_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

/-- The Artin symbol is multiplicative over natural powers. -/
theorem artinSym_pow {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (A : FractionalIdeal (𝓞 K)⁰ K) (hA : A ≠ 0)
    (n : ℕ) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm (A ^ n)
      = (NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact NK.CFTLib.Arl.artinSym_one hcomm
  | succ n ih =>
      rw [pow_succ, NK.CFTLib.Arl.artinSym_mul hcomm (pow_ne_zero n hA) hA, ih, pow_succ]

/-- **The chosen Frobenius element restricts to the chosen Frobenius element of an intermediate
field**, at a prime whose ramification index in the big extension is one. -/
theorem frobAtPrime_restrictNormalHom {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    [IsMulCommutative (Gal(Ω/K))]
    (M : IntermediateField K Ω) [FiniteDimensional K M] [NumberField ↥M] [Normal K M]
    [IsGalois K ↥M] [IsMulCommutative (Gal(↥M/K))]
    (p : NK.Chebotarev.PrimeIdeal K) (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) = 1) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M
        (NK.Chebotarev.frobAtPrime (K := K) (L := Ω) p)
      = NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) p := by
  classical
  have hcommL : ∀ a b : Gal(Ω/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  have hcommM : ∀ a b : Gal(↥M/K), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  have hL : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := Ω) p :=
    (isUnramified_iff_ramificationIdxIn_eq_one p).mpr h
  have hM : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥M) p :=
    isUnramified_intermediateField (K := K) (Ω := Ω) M h
  obtain ⟨σ, hσ⟩ := NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := Ω) p
  have h1 : NK.Chebotarev.frobAtPrime (K := K) (L := Ω) p = σ :=
    (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommL p hL σ).mp hσ
  have h2 : NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) p
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M σ :=
    (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommM p hM _).mp
      (NK.CFTLib.exists_isFrobAtPrime_restrict M hσ)
  rw [h1, h2]

/-- **The Artin symbol is compatible with restriction to an intermediate field**, for fractional
ideals whose prime factors are unramified in the big extension. -/
theorem artinSymFrac_restrictNormalHom {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    [IsMulCommutative (Gal(Ω/K))]
    (M : IntermediateField K Ω) [FiniteDimensional K M] [NumberField ↥M] [Normal K M]
    [IsGalois K ↥M] [IsMulCommutative (Gal(↥M/K))]
    (hcomm : ∀ a b : Gal(Ω/K), a * b = b * a)
    (hcommM : ∀ a b : Gal(↥M/K), a * b = b * a)
    (𝔄 : Frac K)
    (hunr : ∀ p : NK.Chebotarev.PrimeIdeal K,
      NK.CFTLib.Arl.exps (𝔄 : FractionalIdeal (𝓞 K)⁰ K) p ≠ 0 →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) = 1) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M
        (NK.CFTLib.Arl.artinSym (K := K) (L := Ω) hcomm (𝔄 : FractionalIdeal (𝓞 K)⁰ K))
      = NK.CFTLib.Arl.artinSym (K := K) (L := ↥M) hcommM
          (𝔄 : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  let Φ : Frac K →* Gal(Ω/K) := NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcomm
  let ΦM : Frac K →* Gal(↥M/K) := NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcommM
  set S : Finset (NK.Chebotarev.PrimeIdeal K) :=
    (NK.CFTLib.Arl.exps (𝔄 : FractionalIdeal (𝓞 K)⁰ K)).support with hS
  have hfac : 𝔄 = ∏ p ∈ S, (NK.CFTLib.ARL.primeUnit p) ^
      (NK.CFTLib.Arl.exps (𝔄 : FractionalIdeal (𝓞 K)⁰ K)) p := by
    rw [hS]; exact frac_eq_finsupp_prod 𝔄
  have hprime : ∀ p ∈ S,
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M) (Φ (NK.CFTLib.ARL.primeUnit p))
        = ΦM (NK.CFTLib.ARL.primeUnit p) := by
    intro p hp
    have hmem : NK.CFTLib.Arl.exps (𝔄 : FractionalIdeal (𝓞 K)⁰ K) p ≠ 0 :=
      Finsupp.mem_support_iff.mp hp
    simp only [Φ, ΦM, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
      NK.CFTLib.ARL.primeUnit_val]
    rw [NK.CFTLib.Arl.artinSym_prime (K := K) (L := Ω) hcomm p,
      NK.CFTLib.Arl.artinSym_prime (K := K) (L := ↥M) hcommM p]
    exact frobAtPrime_restrictNormalHom (K := K) (Ω := Ω) M p (hunr p hmem)
  have hmain : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M) (Φ 𝔄) = ΦM 𝔄 := by
    conv_lhs => rw [hfac]
    conv_rhs => rw [hfac]
    rw [map_prod Φ, map_prod ΦM, map_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [map_zpow, map_zpow, map_zpow, hprime p hp]
  simpa only [Φ, ΦM, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] using hmain


/-! ## The transfer -/

set_option maxHeartbeats 4000000 in
theorem kernelLe_of_auxField (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsMulCommutative (Gal(L/K))]
    (m : ℕ) (hm : 0 < m) (haux : NK.CFTLib.ARL.AuxFieldHyp K L m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : Gal(L/K) => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m := by
  intro A hcop hsym
  classical
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  set PN : Subgroup (Frac K) :=
    NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRay K L m with hPNdef
  -- the trivial case
  by_cases hA1 : A = 1
  · rw [hA1]; exact Subgroup.one_mem _
  -- the support of `A`
  set s : Finset (NK.Chebotarev.PrimeIdeal K) :=
    (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).support with hsdef
  have hsmem : ∀ 𝔭 ∈ s, (m : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    have h0 : NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K) 𝔭 = 0 := by
      rw [NK.CFTLib.Arl.exps_apply]
      exact hcop 𝔭 hmem
    exact (Finsupp.mem_support_iff.mp h𝔭) h0
  -- the auxiliary-field hypothesis
  obtain ⟨M, hMne, hMcop, -, hMN, hdisjLK, E, hdisjEL, hE𝔭⟩ := haux s hsmem ∅ (by simp)
  haveI hMneI : NeZero M := hMne
  -- a generator of the cyclic group `Gal(L/K)`
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  -- the exponents of the Artin symbols of the primes of `s`
  have hexp : ∀ 𝔭 ∈ s, ∃ t : ℤ, NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 = σ ^ t :=
    fun 𝔭 _ => by
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp (hσ _)
      exact ⟨t, ht.symm⟩
  let sEx : NK.Chebotarev.PrimeIdeal K → ℤ := fun 𝔭 =>
    if h : 𝔭 ∈ s then Classical.choose (hexp 𝔭 h) else 0
  have hsEx : ∀ 𝔭 ∈ s, NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 = σ ^ (sEx 𝔭) := by
    intro 𝔭 h𝔭
    simp only [sEx, dif_pos h𝔭]
    exact Classical.choose_spec (hexp 𝔭 h𝔭)
  -- the Artin symbol of `A` is `σ ^ (Σ e 𝔭 · s 𝔭)`
  set N : ℤ := ∑ 𝔭 ∈ s, (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 * sEx 𝔭
    with hNdef
  have hσN : σ ^ N = 1 := by
    have hΨ : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcomm A = 1 := by
      rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply]
      exact hsym
    have hfac : A = ∏ 𝔭 ∈ s,
        (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K)
          ^ (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 := by
      rw [hsdef]
      exact frac_eq_finsupp_prod A
    have hprimeVal : ∀ 𝔭 ∈ s,
        NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcomm
            (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) = σ ^ (sEx 𝔭) := by
      intro 𝔭 h𝔭
      rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
        show ((idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) : FractionalIdeal (𝓞 K)⁰ K)
          = (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) from rfl,
        NK.CFTLib.Arl.artinSym_prime (K := K) (L := L) hcomm 𝔭]
      exact hsEx 𝔭 h𝔭
    have hkey : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcomm A = σ ^ N := by
      rw [hfac, map_prod, Finset.prod_congr rfl (fun 𝔭 h𝔭 => by
        rw [map_zpow, hprimeVal 𝔭 h𝔭, ← zpow_mul, mul_comm])]
      rw [finset_prod_zpow s σ]
    rw [← hkey]
    exact hΨ
  -- the exponent is a multiple of `[L : K]`
  have hn : Nat.card (Gal(L/K)) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have horder : orderOf σ = Module.finrank K L := by
    rw [← hn]
    exact orderOf_eq_card_of_forall_mem_zpowers hσ
  have hdvd : (Module.finrank K L : ℤ) ∣ N := by
    rw [← horder]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hσN
  -- ### the auxiliary fields `E𝔭`
  have hE' : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      ∃ E𝔭 : IntermediateField K (CyclotomicField M L),
        E𝔭 ≤ E ∧
        (E𝔭.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
          ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
            Set (CyclotomicField M L))) = ⊤ ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥E𝔭) 𝔭.1 1 :=
    fun 𝔭 => hE𝔭 𝔭.1 𝔭.2
  choose Ef hEfle hEfjoin hEfsplit using hE'
  -- the image of `L` in `Ω = L(ζ_M)`
  set LΩ : IntermediateField K (CyclotomicField M L) :=
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K with hLΩdef
  -- `s` is nonempty because `A ≠ 1`
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hA1
    have h0 : NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      rw [Finsupp.ext_iff]
      intro 𝔭
      rw [Finsupp.zero_apply]
      by_contra hne
      have hmem : 𝔭 ∈ s := by rw [hsdef]; exact Finsupp.mem_support_iff.mpr hne
      rw [h] at hmem
      exact Finset.notMem_empty 𝔭 hmem
    rw [frac_eq_finsupp_prod A, h0]
    exact Finsupp.prod_zero_index
  -- the cyclotomic structure of `Ω` over the auxiliary fields
  have hcyc : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      IsCyclotomicExtension {M} ↥(Ef 𝔭) (CyclotomicField M L) :=
    fun 𝔭 => NK.CFTLib.ARLAlt.isCyclotomicExtension_of_sup_adjoin_zeta
      (K := K) (L := L) M (Ef 𝔭) (hEfjoin 𝔭)
  have hcycE : IsCyclotomicExtension {M} ↥E (CyclotomicField M L) := by
    obtain ⟨𝔭₀, h𝔭₀⟩ := hsne
    refine NK.CFTLib.ARLAlt.isCyclotomicExtension_of_sup_adjoin_zeta (K := K) (L := L) M E ?_
    rw [eq_top_iff]
    refine le_trans (le_of_eq (hEfjoin ⟨𝔭₀, h𝔭₀⟩).symm) ?_
    exact sup_le_sup_right (fun x hx => hEfle ⟨𝔭₀, h𝔭₀⟩ hx) _
  -- primes of `↥E𝔭` (resp. `↥E`) not dividing `(M)` are unramified in `Ω`
  have hunr_cyc : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥(Ef 𝔭),
        (M : 𝓞 ↥(Ef 𝔭)) ∉ 𝔮.asIdeal →
        NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥(Ef 𝔭))
          (L := CyclotomicField M L) 𝔮 :=
    fun 𝔭 𝔮 h𝔮 => by
      haveI := hcyc 𝔭
      exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥(Ef 𝔭))
        (Ω := CyclotomicField M L) M 𝔮 h𝔮
  have hunr_cycE : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      (M : 𝓞 ↥E) ∉ 𝔮.asIdeal →
      NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E) (L := CyclotomicField M L) 𝔮 :=
    fun 𝔮 h𝔮 => by
      haveI := hcycE
      exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥E)
        (Ω := CyclotomicField M L) M 𝔮 h𝔮
  -- ### Galois-theoretic setup
  have hdisjEL' : E ⊓ LΩ = ⊥ := disjoint_iff.mp hdisjEL
  haveI hGalΩ0 : IsGalois K (CyclotomicField M L) :=
    NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) (L := L) M
  have hcommΩ : ∀ a b : Gal(CyclotomicField M L / K), a * b = b * a :=
    NK.CFTLib.ARL.mul_comm_cyclotomicField hcomm M
  have hGalF : ∀ F : IntermediateField K (CyclotomicField M L), IsGalois K ↥F :=
    fun F => NK.CFTLib.ARL.isGalois_intermediateField_cyclotomicField_aux hcomm M F
  haveI hGalE : IsGalois K ↥E := hGalF E
  haveI hGalLΩ : IsGalois K ↥LΩ := hGalF LΩ
  haveI hGalΩE : IsGalois ↥E (CyclotomicField M L) :=
    IsGalois.tower_top_of_isGalois K ↥E _
  haveI hfinΩE : FiniteDimensional ↥E (CyclotomicField M L) :=
    IsCyclotomicExtension.finiteDimensional {M} ↥E (CyclotomicField M L)
  haveI habE : IsAbelianGalois ↥E (CyclotomicField M L) :=
    IsCyclotomicExtension.isAbelianGalois {M} ↥E (CyclotomicField M L)
  haveI hcommE' : IsMulCommutative (Gal((CyclotomicField M L)/↥E)) := habE.toIsMulCommutative
  have hcommE : ∀ a b : Gal(CyclotomicField M L / ↥E), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  haveI hcommLΩI : IsMulCommutative (Gal(↥LΩ/K)) := by
    rw [hLΩdef]
    exact NK.CFTLib.ARL.isMulCommutative_LImage (K := K) (L := L) M
  have hcommLΩ : ∀ a b : Gal(↥LΩ/K), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  -- ### the isomorphism `↥LΩ ≃ₐ[K] L` and the conjugate generator
  let eL : ↥LΩ ≃ₐ[K] L := hLΩdef ▸ NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M
  let σΩ : Gal(↥LΩ/K) := NK.CFTLib.ARL.conjHom eL.symm σ
  -- ### the modulus and the ramification hypotheses
  set c : ℕ := m * M with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact Nat.mul_pos hm (NeZero.pos M)
  have hramΩE : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
        (L := CyclotomicField M L) 𝔮 → (c : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
    intro 𝔮 h
    have hM : (M : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
      by_contra hM
      exact h (hunr_cycE 𝔮 hM)
    rw [hcdef, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ hM
  have hramLΩ : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥LΩ) p →
      (c : 𝓞 K) ∈ p.asIdeal := by
    intro p hp
    by_contra hc
    rw [hLΩdef] at hp
    have hm_p : (m : 𝓞 K) ∉ p.asIdeal := fun hmem =>
      hc (by rw [hcdef, Nat.cast_mul]; exact Ideal.mul_mem_right (M : 𝓞 K) p.asIdeal hmem)
    have hM_p : (M : 𝓞 K) ∉ p.asIdeal := fun hmem =>
      hc (by rw [hcdef, Nat.cast_mul]; exact Ideal.mul_mem_left p.asIdeal (m : 𝓞 K) hmem)
    exact hp (NK.CFTLib.ARL.isUnramified_LImage (K := K) (L := L) M m hram p hm_p hM_p)
  -- ### a lift of `σΩ` to `Gal(Ω/↥E)`
  obtain ⟨σ', hσ'⟩ := NK.CFTLib.ARL.restrictNormalHom_comp_restrictScalars_surjective
    (K := K) (Ω := CyclotomicField M L) E LΩ hdisjEL' σΩ
  -- ### the auxiliary ideal `𝔅` and the common norm `𝔟`
  obtain ⟨𝔅, h𝔅ψ⟩ := NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
    (K := ↥E) (L := CyclotomicField M L) c hcpos hramΩE σ'
  have h𝔅cop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := ↥E) c
      (𝔅 : Frac ↥E) :=
    (NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff (K := ↥E) c
      (𝔅 : Frac ↥E)).mp 𝔅.2
  set 𝔟 : Frac K := NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E) (𝔅 : Frac ↥E)
    with h𝔟def
  have hcompat := NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm_of_normal
    (K := K) (M := CyclotomicField M L) E LΩ hcommE hcommLΩ c hramΩE hramLΩ
    (𝔅 : Frac ↥E) h𝔅cop
  have h𝔟ψ : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcommLΩ 𝔟 = σΩ := by
    rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, h𝔟def, ← hcompat, h𝔅ψ]
    simpa only [NK.CFTLib.Arl.restrictScalarsHom_apply, MonoidHom.comp_apply] using hσ'
  -- ### the primes of `s` are coprime to `M`
  have hpM : ∀ 𝔭 ∈ s, (M : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    obtain ⟨p, hp, hpM', hpdvd⟩ := exists_prime_dvd_absNorm_of_mem 𝔭 hmem
    exact hMN p hp hpM' 𝔭 h𝔭 hpdvd
  -- ### `𝔭` is unramified in `↥LΩ`
  have hfrobLΩ : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      NK.Chebotarev.frobAtPrime (K := K) (L := ↥LΩ) 𝔭.1 = σΩ ^ (sEx 𝔭.1) := by
    intro 𝔭
    have h𝔭unr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) 𝔭.1 := by
      by_contra h
      exact hsmem 𝔭.1 𝔭.2 (hram 𝔭.1 h)
    have h𝔭unrΩ : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥LΩ) 𝔭.1 :=
      hLΩdef ▸ NK.CFTLib.ARL.isUnramified_LImage (K := K) (L := L) M m hram 𝔭.1
        (hsmem 𝔭.1 𝔭.2) (hpM 𝔭.1 𝔭.2)
    refine (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommLΩ 𝔭.1 h𝔭unrΩ _).mp ?_
    have h1 : NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭.1 (σ ^ sEx 𝔭.1) := by
      rw [← hsEx 𝔭.1 𝔭.2]
      exact NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm 𝔭.1 h𝔭unr
    have h2 := (NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase (K := K) eL.symm
      (σ ^ sEx 𝔭.1) 𝔭.1).mp h1
    rwa [show (AlgEquiv.symm eL).symm.trans ((σ ^ sEx 𝔭.1).trans eL.symm)
        = σΩ ^ sEx 𝔭.1 from
      map_zpow (NK.CFTLib.ARL.conjHom eL.symm) σ (sEx 𝔭.1)] at h2
  -- ### the `[L : K]`-th power of `𝔟` lies in the norm ray
  have h𝔟cop : FracCoprime m 𝔟 := by
    intro 𝔮 h𝔮
    rw [h𝔟def]
    refine count_relNormUnit_eq_zero (K := K) (E := ↥E) h𝔅cop 𝔮 ?_
    rw [hcdef, Nat.cast_mul]
    exact Ideal.mul_mem_right (M : 𝓞 K) 𝔮.asIdeal h𝔮
  have h𝔟pow : 𝔟 ^ Module.finrank K L ∈
      NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
    NK.Existence.ArtinLemma.pow_finrank_mem_normRay m h𝔟cop
  -- ### the per-prime step
  have hper : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      (idealUnit 𝔭.1.asIdeal 𝔭.1.ne_bot : Frac K) ^
          (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 *
        𝔟 ^ (-((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 * sEx 𝔭.1)) ∈ PN := by
    intro 𝔭
    haveI : IsMulCommutative (Gal(↥LΩ/K)) := hcommLΩI
    -- the tower `↥(Ef 𝔭) ⊆ ↥E`
    letI : Algebra ↥(Ef 𝔭) ↥E := NK.CFTLib.ARL.algOfLe (Ef 𝔭) E (hEfle 𝔭)
    haveI : IsScalarTower K ↥(Ef 𝔭) ↥E :=
      NK.CFTLib.ARL.isScalarTower_algOfLe (Ef 𝔭) E (hEfle 𝔭)
    haveI : FiniteDimensional ↥(Ef 𝔭) ↥E :=
      NK.CFTLib.ARL.finiteDimensional_algOfLe (Ef 𝔭) E (hEfle 𝔭)
    obtain ⟨𝔓, h𝔓lies, h𝔓frob⟩ := hEfsplit 𝔭
    haveI h𝔓over : 𝔓.asIdeal.LiesOver 𝔭.1.asIdeal := h𝔓lies
    have hrelNorm : Ideal.relNorm (𝓞 K) 𝔓.asIdeal = 𝔭.1.asIdeal :=
      NK.CFTLib.ARLAlt.relNorm_prime_eq_of_isFrobAt_one h𝔓lies h𝔓frob
    -- the auxiliary ideal `𝔠 = N_{E𝔭/E}𝔅` and `𝔘 = 𝔓^e·𝔠^{-e·s}`
    set 𝔠 : Frac ↥(Ef 𝔭) :=
      NK.CFTLib.ARL.relNormUnit (K := ↥(Ef 𝔭)) (L := ↥E) (𝔅 : Frac ↥E) with h𝔠def
    set 𝔘 : Frac ↥(Ef 𝔭) :=
      (NK.CFTLib.ARL.primeUnit 𝔓) ^
          (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 *
        𝔠 ^ (-((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 * sEx 𝔭.1)) with h𝔘def
    -- the norm of `𝔘` down to `K`
    have hprime1 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭))
        (NK.CFTLib.ARL.primeUnit 𝔓) = (idealUnit 𝔭.1.asIdeal 𝔭.1.ne_bot : Frac K) := by
      refine Units.ext ?_
      show NK.CFTLib.ARL.relNormFI (K := K) (L := ↥(Ef 𝔭))
          ((NK.CFTLib.ARL.primeUnit 𝔓 : Frac ↥(Ef 𝔭)) :
            FractionalIdeal (𝓞 ↥(Ef 𝔭))⁰ ↥(Ef 𝔭))
        = ((𝔭.1.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      rw [NK.CFTLib.ARL.primeUnit_val, NK.CFTLib.ARL.relNormFI_prime, hrelNorm]
    have h𝔘norm : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)) 𝔘 =
        (idealUnit 𝔭.1.asIdeal 𝔭.1.ne_bot : Frac K) ^
            (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 *
          𝔟 ^ (-((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 * sEx 𝔭.1)) := by
      rw [h𝔘def, map_mul, map_zpow, map_zpow, hprime1, h𝔠def]
      rw [NK.CFTLib.ARL.relNormUnit_trans (K := K) (E := ↥(Ef 𝔭)) (M := ↥E)
        (𝔅 : Frac ↥E), h𝔟def]
    -- the small facts
    have hm𝔭 : (m : 𝓞 K) ∉ 𝔭.1.asIdeal := hsmem 𝔭.1 𝔭.2
    have hpM𝔭 : (M : 𝓞 K) ∉ 𝔭.1.asIdeal := hpM 𝔭.1 𝔭.2
    have hM𝔓 : (M : 𝓞 ↥(Ef 𝔭)) ∉ 𝔓.asIdeal := by
      intro hmem
      have h1 : (M : ℤ) ∈ 𝔓.asIdeal.under ℤ :=
        (Ideal.mem_under ℤ 𝔓.asIdeal).mpr (by simpa using hmem)
      have hunder : 𝔓.asIdeal.under ℤ = 𝔭.1.asIdeal.under ℤ := by
        rw [← Ideal.under_under (A := ℤ) (B := 𝓞 K) 𝔓.asIdeal, ← h𝔓lies.over]
      have h2 : (M : ℤ) ∈ Ideal.span
          {((Ideal.absNorm (𝔭.1.asIdeal.under ℤ) : ℕ) : ℤ)} := by
        rw [Int.ideal_span_absNorm_eq_self, ← hunder]
        exact h1
      exact hMN _ (Nat.absNorm_under_prime 𝔭.1.asIdeal)
        (Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp h2)) 𝔭.1 𝔭.2
        (Int.absNorm_under_dvd_absNorm 𝔭.1.asIdeal)
    have hm𝔓 : (m : 𝓞 ↥(Ef 𝔭)) ∉ 𝔓.asIdeal := by
      intro hmem
      refine hm𝔭 ?_
      rw [Ideal.mem_of_liesOver 𝔓.asIdeal 𝔭.1.asIdeal (m : 𝓞 K), map_natCast]
      exact hmem
    have hc𝔓 : (c : 𝓞 ↥(Ef 𝔭)) ∉ 𝔓.asIdeal := by
      intro hmem
      rw [hcdef, Nat.cast_mul] at hmem
      rcases 𝔓.isPrime.mem_or_mem hmem with h' | h'
      · exact hm𝔓 h'
      · exact hM𝔓 h'
    -- `𝔘` is coprime to `(c)`
    have h𝔠cop : FracCoprime (K := ↥(Ef 𝔭)) c 𝔠 := by
      intro 𝔮 h𝔮
      exact count_relNormUnit_eq_zero (K := ↥(Ef 𝔭)) (E := ↥E) h𝔅cop 𝔮 h𝔮
    have h𝔓cop : FracCoprime (K := ↥(Ef 𝔭)) c (NK.CFTLib.ARL.primeUnit 𝔓) :=
      fracCoprime_primeUnit hc𝔓
    have h𝔘cop : FracCoprime (K := ↥(Ef 𝔭)) c 𝔘 := by
      rw [h𝔘def]
      exact FracCoprime.mul (FracCoprime.zpow _ h𝔓cop) (FracCoprime.zpow _ h𝔠cop)
    -- the cyclotomic structure and commutativity at `E𝔭`
    haveI hcommEpI : IsMulCommutative (Gal((CyclotomicField M L)/↥(Ef 𝔭))) := by
      haveI hab := IsCyclotomicExtension.isAbelianGalois {M} ↥(Ef 𝔭) (CyclotomicField M L)
      exact hab.toIsMulCommutative
    have hcommEp : ∀ a b : Gal(CyclotomicField M L / ↥(Ef 𝔭)), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    haveI hGalΩEp : IsGalois ↥(Ef 𝔭) (CyclotomicField M L) :=
      IsGalois.tower_top_of_isGalois K ↥(Ef 𝔭) _
    haveI hfinΩEp : FiniteDimensional ↥(Ef 𝔭) (CyclotomicField M L) :=
      IsCyclotomicExtension.finiteDimensional {M} ↥(Ef 𝔭) (CyclotomicField M L)
    have hramΩEp : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥(Ef 𝔭),
        ¬NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥(Ef 𝔭))
          (L := CyclotomicField M L) 𝔮 → (c : 𝓞 ↥(Ef 𝔭)) ∈ 𝔮.asIdeal := by
      intro 𝔮 h
      have hMq : (M : 𝓞 ↥(Ef 𝔭)) ∈ 𝔮.asIdeal := by
        by_contra hMq
        exact h (hunr_cyc 𝔭 𝔮 hMq)
      rw [hcdef, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ hMq
    -- the restriction of `ψ_{Ω/E𝔭}(𝔘)` to `LΩ` is trivial
    have hcompatp : AlgEquiv.restrictNormalHom (F := K)
        (K₁ := CyclotomicField M L) LΩ
        ((NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp
            𝔘).restrictScalars K)
        = NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommLΩ
            (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)) 𝔘) :=
      NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm_of_normal
        (K := K) (M := CyclotomicField M L) (Ef 𝔭) LΩ hcommEp hcommLΩ c hramΩEp hramLΩ
        𝔘 h𝔘cop
    have hfrobLΩ' : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcommLΩ
        (idealUnit 𝔭.1.asIdeal 𝔭.1.ne_bot : Frac K) = σΩ ^ (sEx 𝔭.1) := by
      rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
        show ((idealUnit 𝔭.1.asIdeal 𝔭.1.ne_bot : Frac K) : FractionalIdeal (𝓞 K)⁰ K)
          = (𝔭.1.asIdeal : FractionalIdeal (𝓞 K)⁰ K) from rfl,
        NK.CFTLib.Arl.artinSym_prime (K := K) (L := ↥LΩ) hcommLΩ 𝔭.1]
      exact hfrobLΩ 𝔭
    have hN𝔘 : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcommLΩ
        (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)) 𝔘) = 1 := by
      rw [h𝔘norm, map_mul, map_zpow, map_zpow, hfrobLΩ', h𝔟ψ, ← zpow_mul,
        mul_comm (sEx 𝔭.1) ((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1),
        zpow_neg]
      exact mul_inv_cancel _
    have hN𝔘' : NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommLΩ
        (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)) 𝔘) = 1 := by
      rw [← NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply]
      exact hN𝔘
    have hker : AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) LΩ
        ((NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp
            𝔘).restrictScalars K) = 1 := by
      rw [hcompatp, hN𝔘']
    -- `ψ_{Ω/E𝔭}(𝔘)` fixes `LΩ ⊔ E𝔭` pointwise
    have hfixEp : ∀ x ∈ (Ef 𝔭 : Set (CyclotomicField M L)),
        NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp 𝔘 x = x := by
      intro x hx
      exact (NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp
        𝔘).commutes (⟨x, hx⟩ : ↥(Ef 𝔭))
    have hfixLΩ : ∀ x ∈ (LΩ : Set (CyclotomicField M L)),
        NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp 𝔘 x = x := by
      intro x hx
      have h2 := congrArg (fun f : ↥LΩ ≃ₐ[K] ↥LΩ => (f ⟨x, hx⟩ : ↥LΩ)) hker
      have h3 := congrArg (fun z : ↥LΩ => (z : CyclotomicField M L)) h2
      simp only [AlgEquiv.one_apply] at h3
      rw [AlgEquiv.restrictNormalHom_apply] at h3
      exact h3
    have hfixLE : ∀ x ∈ ((Ef 𝔭) ⊔ LΩ : IntermediateField K (CyclotomicField M L)),
        NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp 𝔘 x = x := by
      intro x hx
      have hle : (Ef 𝔭) ⊔ LΩ ≤ IntermediateField.fixedField
          (Subgroup.zpowers ((NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭))
            (L := CyclotomicField M L) hcommEp 𝔘).restrictScalars K)) := by
        refine sup_le ?_ ?_
        · rw [IntermediateField.le_iff_le, Subgroup.zpowers_le,
            IntermediateField.mem_fixingSubgroup_iff]
          intro y hy
          rw [AlgEquiv.restrictScalars_apply]
          exact hfixEp y hy
        · rw [IntermediateField.le_iff_le, Subgroup.zpowers_le,
            IntermediateField.mem_fixingSubgroup_iff]
          intro y hy
          rw [AlgEquiv.restrictScalars_apply]
          exact hfixLΩ y hy
      have h3 : ((NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L)
          hcommEp 𝔘).restrictScalars K) x = x :=
        (IntermediateField.mem_fixedField_iff _ x).mp (hle hx) _ (Subgroup.mem_zpowers _)
      rwa [AlgEquiv.restrictScalars_apply] at h3
    -- the cell's field: Galois and commutative over `E𝔭`
    haveI hcommCellI : IsMulCommutative
        (Gal(↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left)/↥(Ef 𝔭))) :=
      NK.CFTLib.ARLAlt.isMulCommutative_ofLe_sup M (Ef 𝔭) (hEfjoin 𝔭)
    have hcommCell : ∀ a b : Gal(↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭)
        ((Ef 𝔭) ⊔ LΩ) le_sup_left)/↥(Ef 𝔭)), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    haveI hGalCell : IsGalois ↥(Ef 𝔭)
        ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
      NK.CFTLib.ARLAlt.isGalois_ofLe_sup (K := K) (L := L) M (Ef 𝔭)
    -- the Artin symbol of `𝔘` in the cell vanishes
    have h𝔘ψ : NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭))
        (L := ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left))
        hcommCell 𝔘 = 1 := by
      have hR := artinSymFrac_restrictNormalHom (K := ↥(Ef 𝔭))
        (Ω := CyclotomicField M L)
        (M := NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left)
        hcommEp hcommCell 𝔘 (fun q hq => by
          have hMq : (M : 𝓞 ↥(Ef 𝔭)) ∉ q.asIdeal := by
            by_contra hMq
            exact hq (h𝔘cop q (by
              rw [hcdef, Nat.cast_mul]
              exact Ideal.mul_mem_left _ _ hMq))
          exact (isUnramified_iff_ramificationIdxIn_eq_one (K := ↥(Ef 𝔭))
            (L := CyclotomicField M L) q).mp (hunr_cyc 𝔭 q hMq))
      rw [← hR]
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      rw [AlgEquiv.restrictNormalHom_apply]
      exact hfixLE ↑x x.2
    -- the cyclotomic cell at `E𝔭`
    have hcell : 𝔘 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay ↥(Ef 𝔭) c ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay ↥(Ef 𝔭)
          ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) c :=
      NK.CFTLib.ARLAlt.cellAtAuxField (K := K) (L := L) M (Ef 𝔭) (hEfjoin 𝔭) c hcpos
        ⟨m, by rw [hcdef, mul_comm]⟩ (fun q h => by
          have hMq : (M : 𝓞 ↥(Ef 𝔭)) ∈ q.asIdeal := by
            by_contra hMq
            exact h (NK.CFTLib.ARL.isUnramified_cellAtAux M (Ef 𝔭) (hEfjoin 𝔭) q hMq)
          rw [hcdef, Nat.cast_mul]
          exact Ideal.mul_mem_left _ _ hMq) 𝔘 h𝔘cop h𝔘ψ
    -- the norm of `𝔘` down to `K` lies in `P(m)·𝔑(m)`
    rw [← h𝔘norm]
    have hmem : (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)) 𝔘) ∈
        Subgroup.map (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)))
          (NK.CFTLib.ArtinReciprocityIdeal.principalRay ↥(Ef 𝔭) c ⊔
            NK.CFTLib.ArtinReciprocityIdeal.normRay ↥(Ef 𝔭)
              ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) c) :=
      Subgroup.mem_map_of_mem _ hcell
    have hle : Subgroup.map (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)))
        (NK.CFTLib.ArtinReciprocityIdeal.principalRay ↥(Ef 𝔭) c ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay ↥(Ef 𝔭)
            ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) c) ≤ PN := by
      rw [Subgroup.map_sup, hPNdef]
      refine sup_le ?_ ?_
      · exact le_sup_of_le_left (NK.CFTLib.ARLAlt.principalRay_map_relNormUnit_le
          (K := K) (E := ↥(Ef 𝔭)) c m hm hcpos ⟨M, by rw [hcdef]⟩)
      refine le_sup_of_le_right (le_trans ?_ (NK.CFTLib.ARL.normRay_le_of_algEquiv eL.symm m))
      · letI : Algebra ↥LΩ ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭)
            ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
          NK.CFTLib.ARL.algOfLe LΩ ((Ef 𝔭) ⊔ LΩ) le_sup_right
        haveI : IsScalarTower K ↥LΩ
            ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
          NK.CFTLib.ARL.isScalarTower_algOfLe LΩ ((Ef 𝔭) ⊔ LΩ) le_sup_right
        haveI : FiniteDimensional ↥LΩ
            ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
          NK.CFTLib.ARL.finiteDimensional_algOfLe LΩ ((Ef 𝔭) ⊔ LΩ) le_sup_right
        exact NK.CFTLib.ARLAlt.normRay_map_relNormUnit_le (K := K) (L := ↥LΩ)
          (E := ↥(Ef 𝔭))
          (LE := ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left))
          c m hm ⟨M, by rw [hcdef]⟩
    exact hle hmem
  -- ### the product of the `X𝔭`
  have hprod : (∏ 𝔭 ∈ s, (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
      (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭) * 𝔟 ^ (-N) ∈ PN := by
    rw [show (∏ 𝔭 ∈ s, (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
          (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭) * 𝔟 ^ (-N)
        = ∏ 𝔭 ∈ s, ((idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
            (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 *
              𝔟 ^ (-((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 *
                sEx 𝔭))) from ?_]
    · exact Subgroup.prod_mem _ fun 𝔭 h𝔭 => hper ⟨𝔭, h𝔭⟩
    · rw [Finset.prod_mul_distrib, finset_prod_zpow, Finset.sum_neg_distrib, ← hNdef]
  -- ### `𝔟 ^ N ∈ 𝔑(m)`
  have h𝔟N : 𝔟 ^ N ∈ PN := by
    obtain ⟨k, hk⟩ := hdvd
    have h1 : 𝔟 ^ N = (𝔟 ^ Module.finrank K L) ^ k := by
      rw [hk, zpow_mul, zpow_natCast]
    rw [hPNdef, h1]
    exact Subgroup.zpow_mem _ (Subgroup.mem_sup_right h𝔟pow) k
  -- ### conclusion
  rw [hPNdef]
  rw [show A = ∏ 𝔭 ∈ s, (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
      (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 from by
    rw [hsdef]; exact frac_eq_finsupp_prod A]
  have h2 := Subgroup.mul_mem _ hprod h𝔟N
  have h3 : (∏ 𝔭 ∈ s, (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
      (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭) * 𝔟 ^ (-N) * 𝔟 ^ N
      = ∏ 𝔭 ∈ s, (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
        (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 := by
    rw [mul_assoc, zpow_neg, inv_mul_cancel, mul_one]
  rwa [h3] at h2

end NK.CFTLib.ArtinReciprocityIdeal

end

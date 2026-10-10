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
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexIdealCoprimeLeNormClassIndex
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.CFTLib.integralIdelesLeNormImage
import Submission.NK.NUV2.ArtinBridge.continuous_algebraNorm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lang's norm index in ideal form (the lower bound)

This module proves `NK.CFTLib.ArtinReciprocityIdeal.langCyclicRelIndex_proved`:

    `[L : K] ≤ [I^S(m) : P(m)·𝔑(m)]`

for a finite **cyclic** extension `L / K` of number fields and a modulus `m > 0` which is
admissible (`IsAdmissible`) and divisible by all the primes ramified in `L / K`.  This is the
*lower* bound half of Lang's norm index formula (`Lang, ANT, X §2`); the upper bound
`≤ [L : K]` is `NK.CFTLib.ArtinReciprocityIdeal.indexPrincipalRaySupNormRayLe` /
`NK.CFTLib.ARL.index_principalRay_sup_normIdeals_le`.

## Route

The proof works on the idèle side, through the map
`theta : 𝕀 K →* (fractional ideals of K) ⧸ P(m)·𝔑(m)`, `x ↦ (x·(b))` for `b ∈ Kˣ` chosen so that
`x·(b) ≡ 1 mod m` (`NK.CFTLib.ArtinReciprocityIdeal.theta`).  The idèle–ideal dictionary says
that

* `(theta).ker ⊇ Kˣ·N_{L/K} 𝕀_L` — already on disk
  (`principalSubgroup_sup_normImage_le_ker`), and
* `(theta).ker ⊆ Kˣ·N_{L/K} 𝕀_L` when `(m)` is admissible and kills all ramification — this is
  `theta_ker_le` below, the heart of the argument.

Then `[I^S(m) : P(m)·𝔑(m)] = (theta).ker.index = [𝕀_K : Kˣ·N_{L/K}𝕀_L] = [C_K : N C_L] = [L : K]`,
the last equality being `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic` (the reciprocity law for
cyclic extensions).

`theta_ker_le` is proved by running the standard local–global analysis: if `x ∈ (theta).ker` and
`idealOf (x·(b)) = (a)·N_{L/K}(y)`-ideal, then `z := x·(b)·(a)⁻¹·N_{L/K}(y)⁻¹` is an integral idèle
which is a local norm at every place — away from `(m)` because `L/K` is unramified there and `z` is
a local unit, at the primes dividing `(m)` because `z·N_{L/K}(y) ≡ 1 mod m` and `(m)` is admissible,
and at the archimedean places by positivity.  Hasse's norm theorem in the form
`NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm` (locally a norm at every place ⟹ a norm of an
idèle) then puts `z` in `N_{L/K} 𝕀_L`, so `x ∈ Kˣ·N_{L/K}𝕀_L`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped NumberField.LiesOver
open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## 1.  A congruence-norm statement -/

/-- `normIdeleFun` is multiplicative in the idèle. -/
lemma normIdeleFun_mul' (y₁ y₂ : Idele L) (v : Place K) :
    Idele.normIdeleFun K L (y₁ * y₂) v =
      Idele.normIdeleFun K L y₁ v * Idele.normIdeleFun K L y₂ v := by
  rw [← Idele.normIdeleHom_apply, map_mul, Idele.mul_apply, Idele.normIdeleHom_apply,
    Idele.normIdeleHom_apply]

/-- **A congruence-norm statement**: an integral idèle `z` whose product with an idèlic norm
`N_{L/K}(y)` is congruent to `1` modulo `m` at the primes dividing `(m)` and positive at the real
places is itself an idèlic norm. -/
theorem mem_normImage_of_congruence_mul_norm [IsGalois K L] [IsCyclic (Gal(L/K))] {m : ℕ}
    (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m)
    (z : Idele K) (y : Idele L) (hz : z.idealOf = 1)
    (hcong : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      NK.CFTLib.Arl.CongrAt 𝔭 m
        (z (Place.ofFinite 𝔭) * Idele.normIdeleFun K L y (Place.ofFinite 𝔭)))
    (hpos : ∀ w : InfinitePlace K, NK.CFTLib.Arl.PosAtReal w
      (z (Place.ofInfinite w) * Idele.normIdeleFun K L y (Place.ofInfinite w))) :
    z ∈ Idele.normImage K L := by
  classical
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm (K := K) (L := L) z]
  intro v
  rcases v with v | Q
  · -- archimedean
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v :=
      InfinitePlace.comap_surjective v
    have hwl : w.LiesOver v := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w v).mpr hw
    haveI : w.LiesOver v := hwl
    have hdef : Place.localNormInfinite w v
        = Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) := rfl
    have hmem : z (Place.ofInfinite v) * Idele.normIdeleFun K L y (Place.ofInfinite v) ∈
        (Place.localNormInfinite w v).range := by
      rw [hdef]
      rcases v.isReal_or_isComplex with hvR | hvC
      · rcases w.isReal_or_isComplex with hwR | hwC
        · rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real hvR hwR]
          exact Subgroup.mem_top _
        · refine NK.GlobalCFTdeep.NormIndex.localNormInfinite_posSubgroup_le_range_of_real_complex
            hvR hwC ?_
          rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
          exact hpos v hvR
      · have hwC : w.IsComplex :=
          NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
        rw [NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex hvC hwC]
        exact Subgroup.mem_top _
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
    refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
      (Place.ofInfinite w) u * y⁻¹, ?_⟩
    have h1 : Idele.normIdeleFun K L
          (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofInfinite w) u * y⁻¹)
          (Place.ofInfinite v)
        = Place.localNormInfinite w v u * (Idele.normIdeleFun K L y (Place.ofInfinite v))⁻¹ := by
      rw [normIdeleFun_mul', Idele.normIdeleFun_inv_apply,
        NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite v w u]
    rw [h1, hu]
    group
  · -- nonarchimedean
    obtain ⟨q, hq⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
    by_cases hmQ : (m : 𝓞 K) ∈ Q.asIdeal
    · obtain ⟨u, hu⟩ := hadm Q hmQ q hq
        (z (Place.ofFinite Q) * Idele.normIdeleFun K L y (Place.ofFinite Q)) (hcong Q hmQ)
      refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
        (Place.ofFinite q) u * y⁻¹, ?_⟩
      have h1 : Idele.normIdeleFun K L
            (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofFinite q) u * y⁻¹)
            (Place.ofFinite Q)
          = Place.localNormFinite q Q hq u * (Idele.normIdeleFun K L y (Place.ofFinite Q))⁻¹ := by
        rw [normIdeleFun_mul', Idele.normIdeleFun_inv_apply,
          NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q hq u]
      rw [h1, hu]
      group
    · have hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q := by
        by_contra h
        exact hmQ (hram Q h)
      have hzQ : z (Place.ofFinite Q) ∈ Place.localUnits K (Place.ofFinite Q) :=
        Idele.mem_integralIdeles.mp ((Idele.idealOf_eq_one_iff z).mp hz) (Place.ofFinite Q)
          (Place.isFinite_ofFinite Q)
      obtain ⟨u, -, hu⟩ :=
        NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
          Q q hq (hunr q hq) (z (Place.ofFinite Q)) hzQ
      refine ⟨NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofFinite q) u, ?_⟩
      rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q hq u,
        hu]

/-! ## 2.  The norm subgroup and the coprimality of `P(m)·𝔑(m)` -/

/-- A fractional ideal of `L` coprime to `m` has relative norm in the group of ideals of `K`
coprime to `m`. -/
lemma relNormUnit_mem_Icoprime (m : ℕ) {A : (FractionalIdeal (𝓞 L)⁰ L)ˣ}
    (hA : A ∈ NK.CFTLib.ARL.Icoprime L m) :
    NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A ∈ NK.CFTLib.ARL.Icoprime K m := by
  rw [NK.CFTLib.ARL.mem_Icoprime] at hA ⊢
  intro 𝔭 h𝔭
  rw [show ((NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = NK.CFTLib.ARL.relNormFI (K := K) (L := L)
          (A : FractionalIdeal (𝓞 L)⁰ L) from rfl,
    NK.CFTLib.ARL.count_relNormFI, NK.CFTLib.ARL.relNormExp]
  refine Finset.sum_eq_zero (fun 𝔮 h𝔮 => ?_)
  haveI hLO : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := (Place.mem_primesOverFinite).mp h𝔮
  have hmq : (m : 𝓞 L) ∈ 𝔮.asIdeal := by
    have h1 : algebraMap (𝓞 K) (𝓞 L) (m : 𝓞 K) ∈ 𝔮.asIdeal :=
      (Ideal.mem_of_liesOver (p := 𝔭.asIdeal) (P := 𝔮.asIdeal) (m : 𝓞 K)).mp h𝔭
    simpa using h1
  rw [hA 𝔮 hmq, mul_zero]

/-- Every element of `𝔑(m)` is the relative norm of an ideal of `L` coprime to `m`. -/
theorem exists_relNormUnit_of_mem_normIdeals (m : ℕ) {𝔫 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : 𝔫 ∈ NK.CFTLib.ARL.normIdeals K L m) :
    ∃ A ∈ NK.CFTLib.ARL.Icoprime L m, NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A = 𝔫 := by
  have hle : NK.CFTLib.ARL.normIdeals K L m ≤
      (NK.CFTLib.ARL.Icoprime L m).map (NK.CFTLib.ARL.relNormUnit (K := K) (L := L)) := by
    rw [NK.CFTLib.ARL.normIdeals]
    refine (Subgroup.closure_le _).mpr ?_
    rintro A ⟨𝔅, rfl⟩
    obtain ⟨hI, hcop⟩ := 𝔅.2
    refine Subgroup.mem_map.mpr ⟨Units.mk0 ((𝔅.1 : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) (by
      rw [FractionalIdeal.coeIdeal_ne_zero]; exact hI), ?_, ?_⟩
    · rw [NK.CFTLib.ARL.mem_Icoprime]
      intro 𝔓 h𝔓
      rw [Units.val_mk0]
      by_contra hc
      exact hcop 𝔓 h𝔓 ((count_ne_zero_iff_dvd (K := L) hI 𝔓).mp hc)
    · refine Units.ext ?_
      simp only [Units.val_mk0]
      exact NK.CFTLib.ARL.relNormFI_coeIdeal (K := K) (L := L) 𝔅.1 hI
  obtain ⟨A, hA, hAeq⟩ := Subgroup.mem_map.mp (hle h)
  exact ⟨A, hA, hAeq⟩

/-- **The first conjunct**: `P(m)·𝔑(m) ⊆ I(m)`. -/
theorem principalRay_sup_normRay_le_idealCoprimeGroup (m : ℕ) :
    (NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m) ≤
      NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m := by
  rw [NK.CFTLib.ArtinReciprocityIdeal.principalRay_eq_ARL,
    NK.CFTLib.ArtinReciprocityIdeal.normRay_eq_normIdeals,
    NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup_eq_Icoprime]
  refine sup_le ?_ ?_
  · intro A hA
    obtain ⟨a, haU, rfl⟩ := Subgroup.mem_map.mp hA
    rw [NK.CFTLib.ARL.mem_Icoprime]
    intro 𝔭 h𝔭
    rw [NK.CFTLib.ARL.unitsToIdealUnits_coe, ← Idele.idealOf_principalIdele]
    exact NK.CFTLib.ARL.count_idealOf_eq_zero_of_congruence (Subgroup.mem_comap.mp haU) 𝔭 h𝔭
  · intro 𝔫 h𝔫
    obtain ⟨A, hA, rfl⟩ := exists_relNormUnit_of_mem_normIdeals (K := K) (L := L) m h𝔫
    exact relNormUnit_mem_Icoprime (K := K) (L := L) m hA

/-! ## 3.  The kernel of `θ` -/

/-- **The kernel of `θ` is contained in `Kˣ · 𝔑`** (the idèle–ideal dictionary, Milne Prop. 4.6). -/
theorem theta_ker_le [IsGalois K L] [IsCyclic (Gal(L/K))] (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m) :
    (NK.CFTLib.ArtinReciprocityIdeal.theta K L m hm).ker ≤
      Idele.principalSubgroup K ⊔ Idele.normImage K L := by
  classical
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  -- the adjusted idèle `xb = x·(b)`
  have hxb : x * Idele.principalIdele K (adjId K m hm x) ∈
      NK.CFTLib.Arl.congruenceSubgroup K m := adjId_spec (K := K) m hm x
  have hmem : IdeleClassGroup.idealOfUnitHom K
      (x * Idele.principalIdele K (adjId K m hm x)) ∈ rayNorm K L m := by
    have h := hx
    rw [show (theta K L m hm) x = QuotientGroup.mk' (rayNorm K L m)
        (IdeleClassGroup.idealOfUnitHom K
          (x * Idele.principalIdele K (adjId K m hm x))) from rfl] at h
    rw [QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨𝔭, h𝔭P, 𝔫, h𝔫N, hprod⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨a, haU, haEq⟩ := Subgroup.mem_map.mp h𝔭P
  have haU' : Idele.principalIdele K a ∈ NK.CFTLib.Arl.congruenceSubgroup K m :=
    Subgroup.mem_comap.mp haU
  obtain ⟨A, hA, hAeq⟩ := exists_relNormUnit_of_mem_normIdeals (K := K) (L := L) m h𝔫N
  obtain ⟨y, -, hyA⟩ := NK.CFTLib.ARL.exists_idealOf_eq_of_mem_Icoprime (K := L) (m := m) hm ⟨A, hA⟩
  have hyid : Idele.idealOf y = (A : FractionalIdeal (𝓞 L)⁰ L) := by
    have h := congrArg (fun u : (FractionalIdeal (𝓞 L)⁰ L)ˣ =>
      (u : FractionalIdeal (𝓞 L)⁰ L)) hyA
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0] at h
    exact h
  have hNy : Idele.idealOf (Idele.normIdeleHom K L y) = (𝔫 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [NK.CFTLib.ARL.idealOf_normIdeleHom, hyid]
    rw [show NK.CFTLib.ARL.relNormFI (K := K) (L := L) (A : FractionalIdeal (𝓞 L)⁰ L)
        = ((NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A :
            (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) from rfl, hAeq]
  -- the integral idèle `z`
  set xb : Idele K := x * Idele.principalIdele K (adjId K m hm x) with hxbdef
  have hxb' : xb ∈ NK.CFTLib.Arl.congruenceSubgroup K m := hxb
  set z : Idele K := xb * (Idele.principalIdele K a)⁻¹ * (Idele.normIdeleHom K L y)⁻¹ with hzdef
  have hzU : IdeleClassGroup.idealOfUnitHom K z = 1 := by
    have h𝔞 : IdeleClassGroup.idealOfUnitHom K xb = 𝔭 * 𝔫 := by
      rw [hxbdef, ← hprod]
    have hNyU : IdeleClassGroup.idealOfUnitHom K (Idele.normIdeleHom K L y) = 𝔫 := by
      refine Units.ext ?_
      rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, hNy]
    rw [hzdef, map_mul, map_mul, map_inv, map_inv,
      NK.CFTLib.ARL.idealOfUnitHom_principalIdele, haEq, h𝔞, hNyU]
    rw [mul_assoc 𝔭 𝔫 𝔭⁻¹, mul_comm 𝔫 𝔭⁻¹, ← mul_assoc 𝔭 𝔭⁻¹ 𝔫, mul_inv_cancel, one_mul,
      mul_inv_cancel]
  have hz : z.idealOf = 1 := by
    have h := congrArg (fun u : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
      (u : FractionalIdeal (𝓞 K)⁰ K)) hzU
    rw [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0, Units.val_one] at h
    exact h
  have hzw : ∀ v : Place K, z v * Idele.normIdeleFun K L y v
      = (xb * (Idele.principalIdele K a)⁻¹) v := by
    intro v
    rw [hzdef]
    simp only [Idele.mul_apply, Idele.inv_apply, Idele.normIdeleHom_apply]
    group
  have hcong : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      NK.CFTLib.Arl.CongrAt 𝔭 m
        (z (Place.ofFinite 𝔭) * Idele.normIdeleFun K L y (Place.ofFinite 𝔭)) := by
    intro 𝔭 h𝔭
    rw [hzw (Place.ofFinite 𝔭)]
    exact (Subgroup.mul_mem _ hxb' (Subgroup.inv_mem _ haU')).1 𝔭 h𝔭
  have hpos : ∀ w : InfinitePlace K, NK.CFTLib.Arl.PosAtReal w
      (z (Place.ofInfinite w) * Idele.normIdeleFun K L y (Place.ofInfinite w)) := by
    intro w
    rw [hzw (Place.ofInfinite w)]
    exact (Subgroup.mul_mem _ hxb' (Subgroup.inv_mem _ haU')).2 w
  have hznorm : z ∈ Idele.normImage K L :=
    mem_normImage_of_congruence_mul_norm (K := K) (L := L) hm hram hadm z y hz hcong hpos
  -- assembly
  have hxb_decomp : xb = z * Idele.normIdeleHom K L y * Idele.principalIdele K a := by
    rw [hzdef]
    group
  have hxb_mem : xb ∈ Idele.principalSubgroup K ⊔ Idele.normImage K L := by
    rw [hxb_decomp]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hznorm) ?_)
      (Subgroup.mem_sup_left (Idele.mem_principalSubgroup.mpr ⟨a, rfl⟩))
    refine Subgroup.mem_sup_right ?_
    rw [Idele.normImage_eq_range]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  have hx_eq : x = xb * (Idele.principalIdele K (adjId K m hm x))⁻¹ := by
    rw [hxbdef]
    group
  rw [hx_eq]
  exact Subgroup.mul_mem _ hxb_mem
    (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Idele.mem_principalSubgroup.mpr ⟨_, rfl⟩)))

/-! ## 4.  The main statement -/

/-- **Lang's norm index in ideal form** (Lang, *Algebraic Number Theory*, Ch. IX §5, as used in
Ch. X §2): for a finite cyclic extension `L / K` of number fields and a modulus `m > 0` divisible by
all the primes ramified in `L / K` and admissible, the subgroup `P(m) ⊔ 𝔑(m)` of the group
`I^S(m) = idealCoprimeGroup K m` of fractional ideals coprime to `(m)` is contained in `I^S(m)` and
has relative index at least `[L : K]`:

  `[L : K] ≤ (principalRay K m ⊔ normRay K L m).relIndex (idealCoprimeGroup K m)`,

where `principalRay K m = P(m)` is the group of principal ideals `(a)` with `a ≡ 1 mod (m)` and
totally positive, and `normRay K L m = 𝔑(m)` is the group generated by the relative norms
`N_{L/K}(𝔮)` of the ideals `𝔮` of `L` coprime to `(m)`.

This is the *lower* bound half of the conductor index computation; the upper bound `≤ [L:K]` is
Milne, *CFT*, Theorem 4.9, formalised in this directory as `indexPrincipalRaySupNormRayLe`.  The two
together, with the surjectivity `[I^S(m) : ker ψ] = [L:K]` of the ideal-theoretic Artin symbol, give
`ker ψ = P(m)·𝔑(m)`, hence the conductor result `artinKillsPrincipal_cyclic` and then the
ideal-theoretic reciprocity law `NK.CFTLib.ArtinReciprocityIdeal` — the single missing input of
global class field theory in this workspace.

**Route.**  Work on the idèle side; the cyclic index formula
`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic` is unconditional:
`[C_K : N_{L/K}C_L] = [L:K]`.  The ideals coprime to `(m)` correspond to idèles by
`NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists` (with the weak-approximation
adjustment `NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust`), and this dictionary identifies
`I^S(m) ⧸ (P(m)·𝔑(m))` with the idèle quotient `𝕀_K ⧸ (Kˣ·W_m·N_{L/K}𝕀_L)`, where `W_m` is the
subgroup of idèles that are units away from `(m)` and congruent to `1` at the primes dividing `(m)`.
The hypotheses give `W_m ⊆ N_{L/K}𝕀_L`: away from `(m)` every local unit is a local norm because
`L/K` is unramified there (`hram`), and at the primes dividing `(m)` the admissibility `hadm`
supplies the congruence/conductor level; Hasse's norm principle for cyclic extensions then upgrades
these local conditions to `Kˣ·W_m·N_{L/K}𝕀_L = Kˣ·N_{L/K}𝕀_L`.  Hence
`[I^S(m) : P(m)·𝔑(m)] = [𝕀_K : Kˣ·N_{L/K}𝕀_L] = [L:K]`, which is the claimed lower bound. -/
theorem langCyclicRelIndex_proved (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L/K))] (m : ℕ)
    (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m) :
    (NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m) ≤
      NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m ∧
    Module.finrank K L ≤ (NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).relIndex
      (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m) := by
  have hker_le : (theta K L m hm).ker ≤ Idele.principalSubgroup K ⊔ Idele.normImage K L :=
    theta_ker_le (K := K) (L := L) m hm hram hadm
  have hker_ge : Idele.principalSubgroup K ⊔ Idele.normImage K L ≤ (theta K L m hm).ker :=
    principalSubgroup_sup_normImage_le_ker (K := K) (L := L) m hm
  have hker_eq : (theta K L m hm).ker =
      Idele.principalSubgroup K ⊔ Idele.normImage K L := le_antisymm hker_le hker_ge
  refine ⟨principalRay_sup_normRay_le_idealCoprimeGroup (K := K) (L := L) m, ?_⟩
  calc Module.finrank K L
      = (Idele.normClassSubgroup K L).index :=
        (NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := K) (L := L)).symm
    _ = (Idele.principalSubgroup K ⊔ Idele.normImage K L).index :=
        (index_principalSubgroup_sup_normImage (K := K) (L := L) m).symm
    _ = (theta K L m hm).ker.index := by rw [hker_eq]
    _ = ((rayNorm K L m).subgroupOf (NK.CFTLib.ARL.Icoprime K m)).index :=
        (index_rayNorm_eq_ker_index (K := K) (L := L) m hm).symm
    _ = ((NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).subgroupOf
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m)).index := by
        rw [rayNorm, NK.CFTLib.ArtinReciprocityIdeal.principalRay_eq_ARL,
          NK.CFTLib.ArtinReciprocityIdeal.normRay_eq_normIdeals,
          NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup_eq_Icoprime]
    _ ≤ (NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).relIndex
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m) := le_of_eq rfl

end NK.CFTLib.ArtinReciprocityIdeal

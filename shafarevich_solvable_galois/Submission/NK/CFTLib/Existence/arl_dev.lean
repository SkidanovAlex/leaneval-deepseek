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
import Submission.NK.CFTLib.Existence.res_inf_le_ker_res_of_auxiliary
import Submission.NK.NUV2.ARL.normAdjustment

/-!
# Components of the proof of `NK.CFTLib.Existence.arl_invariants`

This module collects the verified components of the arithmetic input `NK.CFTLib.Existence.arl_invariants`
(the Verlagerung input of Route B): the Galois-theoretic bookkeeping for the complementary pair
`(Msub, Nsub)`, the per-prime Frobenius product computation (an improvement of
`NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one` where the unramifiedness hypothesis is at
`𝔭` in `E/K` rather than in `M/K`), and the computation of the Artin symbol of an extended ideal.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped NumberField Pointwise nonZeroDivisors
open NumberField IntermediateField IsDedekindDomain

namespace NK.CFTLib.Arl

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
  [FiniteDimensional K Ω] [IsGalois K Ω]

/-- `|Msub| = |Gal(L/K)|`. -/
lemma card_Msub_eq (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hdisj : fixedField Msub ⊓ fixedField Nsub = ⊥)
    (hsup : fixedField Msub ⊔ fixedField Nsub = ⊤) :
    Nat.card ↥Msub = Nat.card Gal(L/K) := by
  have hcard := NK.CFTLib.Existence.card_mul_card_eq Msub Nsub hdisj hsup
  have hG : Nat.card Gal(Ω/K) = Nat.card ↥Nsub * Nat.card (Gal(Ω/K) ⧸ Nsub) := by
    rw [← Subgroup.index_eq_card]; exact (Subgroup.card_mul_index Nsub).symm
  have key : Nat.card ↥Nsub * Nat.card ↥Msub
      = Nat.card ↥Nsub * Nat.card (Gal(Ω/K) ⧸ Nsub) := by
    rw [mul_comm (Nat.card ↥Nsub), hcard, hG]
  have h1 : Nat.card ↥Msub = Nat.card (Gal(Ω/K) ⧸ Nsub) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos key
  rw [h1, hN]

/-- The exponent of `Gal(Ω/K)` divides `n`. -/
lemma pow_card_eq_one (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hdisj : fixedField Msub ⊓ fixedField Nsub = ⊥)
    (hsup : fixedField Msub ⊔ fixedField Nsub = ⊤) :
    ∀ g : Gal(Ω/K), g ^ Nat.card Gal(L/K) = 1 := by
  have hMN : Msub ⊔ Nsub = ⊤ := NK.CFTLib.Existence.sup_eq_top_of_fixedField_inf_eq_bot Msub Nsub hdisj
  have hMiN : Msub ⊓ Nsub = ⊥ := NK.CFTLib.Existence.inf_eq_bot_of_fixedField_sup_eq_top Msub Nsub hsup
  have hcardN : Nat.card ↥Nsub = Nat.card Gal(L/K) :=
    (NK.CFTLib.Existence.card_nsub_eq_card_quotient Msub Nsub hdisj hsup).trans hM
  have hcardM : Nat.card ↥Msub = Nat.card Gal(L/K) := card_Msub_eq Msub Nsub hN hdisj hsup
  intro g
  have hg : g ∈ (Msub : Set Gal(Ω/K)) * (Nsub : Set Gal(Ω/K)) := by
    rw [← Subgroup.mul_normal Msub Nsub, hMN]; trivial
  obtain ⟨m, hm, n, hn, rfl⟩ := Set.mem_mul.mp hg
  have hcomm : Commute m n := Subgroup.commute_of_normal_of_disjoint _ _
    (inferInstance : Msub.Normal) (inferInstance : Nsub.Normal)
    (disjoint_iff_inf_le.mpr (by rw [hMiN])) m n hm hn
  rw [hcomm.mul_pow]
  have hm1 : m ^ Nat.card Gal(L/K) = 1 := by
    have h : (⟨m, hm⟩ : ↥Msub) ^ Nat.card ↥Msub = 1 := pow_card_eq_one'
    rw [hcardM] at h
    simpa using Subtype.ext_iff.mp h
  have hn1 : n ^ Nat.card Gal(L/K) = 1 := by
    have h : (⟨n, hn⟩ : ↥Nsub) ^ Nat.card ↥Nsub = 1 := pow_card_eq_one'
    rw [hcardN] at h
    simpa using Subtype.ext_iff.mp h
  rw [hm1, hn1, mul_one]



/-- The product of the Frobenius elements of `E/L₀` at the primes of `L₀` above a prime `𝔭` of `K`
which is unramified in `E/K`, raised to the ramification indices, is trivial. -/
theorem prod_frobAtPrime_pow_eq_one_of_unramified {K E : Type} [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (L₀ M : IntermediateField K E) [IsGalois K ↥L₀] [IsGalois K ↥M]
    [IsMulCommutative Gal(↥M/K)]
    (hdisj : L₀ ⊓ M = ⊥) (hsup : L₀ ⊔ M = ⊤)
    (hcard : Nat.card Gal(↥L₀/K) = Nat.card Gal(↥M/K))
    (hexp : ∀ σ : Gal(↥M/K), σ ^ Module.finrank K ↥L₀ = 1)
    (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (hunr : ∀ 𝔓 : NK.Chebotarev.PrimeIdeal E,
      𝔓.asIdeal.LiesOver 𝔭.asIdeal → 𝔓.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (List.map (fun 𝔮 => (NK.Chebotarev.frobAtPrime (K := ↥L₀) (L := E) 𝔮) ^
      (𝔮.asIdeal.ramificationIdx (𝓞 K)))
      (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L₀) 𝔭).toList).prod = 1 := by
  classical
  haveI hfdL0 : FiniteDimensional K ↥L₀ := IsGalois.finiteDimensional_of_finite K ↥L₀
  haveI hfdM : FiniteDimensional K ↥M := IsGalois.finiteDimensional_of_finite K ↥M
  refine NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one L₀ M hdisj hsup hexp 𝔭 ?_ ?_
  · -- `𝔭` is unramified in `M/K`
    intro Q hQ
    obtain ⟨𝔓, h𝔓⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := ↥M) (L := E) Q
    haveI h𝔓Q : 𝔓.asIdeal.LiesOver Q.asIdeal := h𝔓
    haveI hQ𝔭 : Q.asIdeal.LiesOver 𝔭.asIdeal := hQ
    have h𝔓𝔭 : 𝔓.asIdeal.LiesOver 𝔭.asIdeal :=
      Ideal.LiesOver.trans 𝔓.asIdeal Q.asIdeal 𝔭.asIdeal
    have h1 : 𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := hunr 𝔓 h𝔓𝔭
    have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 ↥M) (T := 𝓞 E)
      Q.asIdeal 𝔓.asIdeal
    rw [h1] at htower
    exact (mul_eq_one.mp htower.symm).1
  · -- `E/L₀` is unramified above `𝔭`
    intro 𝔮 h𝔮 𝔔 h𝔔
    have h𝔮𝔭 : 𝔮.asIdeal.LiesOver 𝔭.asIdeal :=
      (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := ↥L₀) (Q := 𝔭) (q := 𝔮)).mp h𝔮
    haveI h𝔔𝔮 : 𝔔.asIdeal.LiesOver 𝔮.asIdeal := h𝔔
    haveI h𝔮𝔭' : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := h𝔮𝔭
    have h𝔓𝔭 : 𝔔.asIdeal.LiesOver 𝔭.asIdeal :=
      Ideal.LiesOver.trans 𝔔.asIdeal 𝔮.asIdeal 𝔭.asIdeal
    have h1 : 𝔔.asIdeal.ramificationIdx (𝓞 K) = 1 := hunr 𝔔 h𝔓𝔭
    have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 ↥L₀) (T := 𝓞 E)
      𝔮.asIdeal 𝔔.asIdeal
    rw [h1] at htower
    exact (mul_eq_one.mp htower.symm).2


/-- Powers of a list of pairwise commuting elements factor out. -/
lemma List.prod_map_zpow {G ι : Type*} [Group G] (l : List ι) (f : ι → G)
    (hcomm : ∀ a b : G, a * b = b * a) (v : ℤ) :
    (l.map (fun x => f x ^ v)).prod = ((l.map f).prod) ^ v := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih]
      have hc : Commute (f a) ((l.map f).prod) := hcomm _ _
      exact (hc.mul_zpow v).symm

/-- **The Artin symbol of the extended ideal.** -/
theorem artinSym_idealOf_ideleInclusion_eq_one {K L E : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [Field E] [NumberField E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    [FiniteDimensional L E] [IsGalois L E]
    (hcomm : ∀ a b : Gal(E/L), a * b = b * a)
    (u : NK.GlobalCFT.Place L → NK.GlobalCFT.Place K)
    (hu : ∀ w : NK.GlobalCFT.Place L, w.LiesOver (u w))
    (φ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele L)
    (hφ : ∀ (x : NK.GlobalCFT.Idele K) (w : NK.GlobalCFT.Place L),
      φ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (M : ℕ)
    (hterm : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, (M : 𝓞 K) ∉ 𝔭.asIdeal →
      (List.map (fun 𝔮 : NK.Chebotarev.PrimeIdeal L =>
          (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^
            (𝔮.asIdeal.ramificationIdx (𝓞 K)))
        (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭).toList).prod = 1)
    (x : NK.GlobalCFT.Idele K)
    (hMsupp : ∀ 𝔮 ∈ (exps (NK.GlobalCFT.Idele.idealOf (φ x))).support,
      (M : 𝓞 K) ∉ (𝔮.under (𝓞 K)).asIdeal) :
    artinSym hcomm (NK.GlobalCFT.Idele.idealOf (φ x)) = 1 := by
  classical
  letI : CommMonoid Gal(E/L) := galCommMonoid hcomm
  set A := NK.GlobalCFT.Idele.idealOf (φ x) with hA
  have hunfold : artinSym hcomm A
      = ∏ 𝔮 ∈ (exps A).support,
          (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^ ((exps A) 𝔮) := by
    rw [artinSym]
    exact Finsupp.prod_of_support_subset _ le_rfl _ (fun i _ => zpow_zero _)
  rw [hunfold]
  -- group the product over `L` by the prime of `K` below
  rw [← Finset.prod_fiberwise_of_maps_to
    (s := (exps A).support)
    (t := (exps A).support.image (fun 𝔮 : NK.Chebotarev.PrimeIdeal L => 𝔮.under (𝓞 K)))
    (g := fun 𝔮 : NK.Chebotarev.PrimeIdeal L => 𝔮.under (𝓞 K))
    (f := fun 𝔮 => (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^ ((exps A) 𝔮))
    (fun i hi => Finset.mem_image_of_mem _ hi)]
  refine Finset.prod_eq_one ?_
  rintro 𝔭 h𝔭
  obtain ⟨𝔮₀, h𝔮₀s, h𝔮₀u⟩ := Finset.mem_image.mp h𝔭
  have hM𝔭 : (M : 𝓞 K) ∉ 𝔭.asIdeal := by
    rw [← h𝔮₀u]
    exact hMsupp 𝔮₀ h𝔮₀s
  set v : ℤ := FractionalIdeal.count K 𝔭 (NK.GlobalCFT.Idele.idealOf x) with hv
  have hfib : (exps A).support.filter (fun 𝔮 : NK.Chebotarev.PrimeIdeal L => 𝔮.under (𝓞 K) = 𝔭)
      ⊆ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭 := by
    intro 𝔮 h𝔮
    rw [Finset.mem_filter] at h𝔮
    rw [NK.GlobalCFT.Place.mem_primesOverFinite]
    exact Ideal.LiesOver.mk (by
      rw [← h𝔮.2, IsDedekindDomain.HeightOneSpectrum.under_asIdeal])
  have hprod : (∏ 𝔮 ∈ (exps A).support.filter
        (fun 𝔮 : NK.Chebotarev.PrimeIdeal L => 𝔮.under (𝓞 K) = 𝔭),
        (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^ ((exps A) 𝔮))
      = ∏ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭,
          (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^ ((exps A) 𝔮) := by
    refine (Finset.prod_subset
      (f := fun 𝔮 : NK.Chebotarev.PrimeIdeal L =>
        (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^ ((exps A) 𝔮)) hfib ?_)
    intro 𝔮 h𝔮T h𝔮S
    have hzero : (exps A) 𝔮 = 0 := by
      by_contra hne
      apply h𝔮S
      rw [Finset.mem_filter]
      refine ⟨(Finsupp.mem_support_iff).mpr hne, ?_⟩
      have hlies := (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L)
        (Q := 𝔭) (q := 𝔮)).mp h𝔮T
      refine IsDedekindDomain.HeightOneSpectrum.ext ?_
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact hlies.over.symm
    rw [hzero, zpow_zero]
    rfl
  rw [hprod]
  have hcount : ∀ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭,
      (exps A) 𝔮 = (𝔮.asIdeal.ramificationIdx (𝓞 K) : ℤ) * v := by
    intro 𝔮 h𝔮
    have hlies := (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L)
      (Q := 𝔭) (q := 𝔮)).mp h𝔮
    rw [NK.CFTLib.Arl.exps_apply]
    exact NK.CFTLib.Existence.count_idealOf_ideleInclusion u hu φ hφ x 𝔭 𝔮 hlies
  rw [Finset.prod_congr rfl (fun 𝔮 h𝔮 => by rw [hcount 𝔮 h𝔮, zpow_mul])]
  rw [← Finset.prod_map_toList
    (f := fun 𝔮 : NK.Chebotarev.PrimeIdeal L =>
      ((NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^
        ((𝔮.asIdeal.ramificationIdx (𝓞 K) : ℤ))) ^ v)]
  refine (show (List.map (fun 𝔮 : NK.Chebotarev.PrimeIdeal L =>
          ((NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^
            ((𝔮.asIdeal.ramificationIdx (𝓞 K) : ℤ))) ^ v)
        (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭).toList).prod
      = ((List.map (fun 𝔮 : NK.Chebotarev.PrimeIdeal L =>
          (NK.Chebotarev.frobAtPrime (K := L) (L := E) 𝔮) ^
            ((𝔮.asIdeal.ramificationIdx (𝓞 K) : ℤ)))
        (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭).toList).prod) ^ v
    from NK.CFTLib.Arl.List.prod_map_zpow _ _ hcomm v).trans ?_
  simp only [zpow_natCast]
  rw [hterm 𝔭 hM𝔭, one_zpow]
  rfl



/-! ## Galois-theoretic data for the complementary pair -/

/-- The exponential structure of `Ω/K`. -/
lemma galois_data (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hdisj : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥)
    (hsup : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤) :
    Nat.card ↥Nsub = Nat.card Gal(L/K) ∧
    Nat.card ↥Msub = Nat.card Gal(L/K) ∧
    (∀ g : Gal(Ω/K), g ^ Nat.card Gal(L/K) = 1) ∧
    Msub ⊔ Nsub = ⊤ ∧ Msub ⊓ Nsub = ⊥ :=
  ⟨(NK.CFTLib.Existence.card_nsub_eq_card_quotient Msub Nsub hdisj hsup).trans hM,
   card_Msub_eq Msub Nsub hN hdisj hsup,
   pow_card_eq_one Msub Nsub hN hM hdisj hsup,
   NK.CFTLib.Existence.sup_eq_top_of_fixedField_inf_eq_bot Msub Nsub hdisj,
   NK.CFTLib.Existence.inf_eq_bot_of_fixedField_sup_eq_top Msub Nsub hsup⟩

/-- `Gal(Ω/L') ≅ Nsub` for `L' = fixedField Nsub`. -/
lemma galois_fixedField_equiv (Nsub : Subgroup Gal(Ω/K)) [Nsub.Normal] :
    Nonempty (Gal(Ω/↥(IntermediateField.fixedField Nsub)) ≃* ↥Nsub) :=
  ⟨(IntermediateField.subgroupEquivAlgEquiv Nsub).symm⟩

/-- `Gal(M'/K)` is commutative for `M' = fixedField Msub`, when `Gal(Ω/K)/Msub` is cyclic. -/
lemma isMulCommutative_fixedField (Msub : Subgroup Gal(Ω/K)) [Msub.Normal]
    (hcyc : IsCyclic (Gal(Ω/K) ⧸ Msub)) :
    IsMulCommutative Gal(↥(IntermediateField.fixedField Msub)/K) := by
  haveI : IsCyclic Gal(↥(IntermediateField.fixedField Msub)/K) :=
    (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient Msub)).mp hcyc
  exact IsCyclic.isMulCommutative

/-! ## The modulus enlargement: a prime ramified in `Ω/K` divides `N(𝔡_{Ω/K})` -/

/-- A prime of `K` ramified in `Ω/K` divides the different-number `N(𝔡_{Ω/K})`. -/
lemma absNorm_differentIdeal_mem_of_ramified {p : NK.Chebotarev.PrimeIdeal K}
    (hp : Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) ≠ 1) :
    ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 Ω)) : ℕ) : 𝓞 K) ∈ p.asIdeal := by
  by_contra hmem
  exact hp (NK.CFTLib.ramificationIdxIn_eq_one_of_absNorm_differentIdeal_notMem p hmem)

lemma absNorm_differentIdeal_pos :
    0 < Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 Ω)) := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  exact differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 Ω) (Ideal.absNorm_eq_zero_iff.mp h0)

end NK.CFTLib.Arl

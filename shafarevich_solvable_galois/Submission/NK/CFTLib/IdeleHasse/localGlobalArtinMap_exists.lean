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
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.CFTLib.IdeleHasse.exists_localMap_ofFinite
import Submission.NK.CFTLib.IdeleHasse.ideleGluing
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.NK.NUV2.ArtinBridge.continuous_algebraNorm
import Submission.NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormInfinite_range
import Submission.NK.NUV2.ArtinBridge.localUnits_le_image_localNormFinite_of_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical local–global Artin map of a cyclic extension

For a cyclic extension `L / K` of number fields this file produces the canonical local–global
Artin map `Φ : 𝕀 K →* Gal(L/K)`: the product `∏_v λ_v` of the local Artin maps, glued along the
idèles.  The four structural clauses (surjectivity, triviality on the idèlic norms, faithfulness at
one place, and Frobenius normalisation at the unramified primes) are proved in
`exists_localGlobalArtinMap_aux` below; the only arithmetic input it needs is the local Artin map
at each archimedean place, which is supplied here (`exists_localMap_ofInfinite`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.IdeleHasse

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Auxiliary lemmas -/

/-- The `v`-component of the norm idèle lies in the local norm subgroup. -/
theorem normIdeleFun_mem_localNormSubgroup (y : Idele L) (v : Place K) :
    Idele.normIdeleFun K L y v ∈ localNormSubgroup (K := K) (L := L) v := by
  classical
  cases v with
  | inl w =>
      rw [Idele.normIdeleFun_ofInfinite, localNormSubgroup_ofInfinite (K := K) (L := L)]
      refine Subgroup.prod_mem _ fun w' _ => ?_
      exact Subgroup.mem_iSup_of_mem
        ⟨w'.1, (Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := w'.1)).mp w'.2⟩
        (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  | inr Q =>
      rw [Idele.normIdeleFun_ofFinite, localNormSubgroup_ofFinite (K := K) (L := L)]
      refine Subgroup.prod_mem _ fun q' _ => ?_
      exact Subgroup.mem_iSup_of_mem
        ⟨q'.1, (Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q'.1)).mp q'.2⟩
        (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

/-- At an unramified finite place the local units are local norms. -/
theorem localUnits_le_localNormSubgroup_of_unramified (Q : HeightOneSpectrum (𝓞 K))
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) :
    Place.localUnits K (Place.ofFinite Q) ≤
      localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) := by
  obtain ⟨q, hq⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
  have he : q.asIdeal.ramificationIdx (𝓞 K) = 1 := hunr q hq
  intro a ha
  obtain ⟨u, _hu, hua⟩ :=
    NK.NUV2.ArtinBridge.localUnits_le_image_localNormFinite_of_ramificationIdx_eq_one
      q Q hq he a ha
  rw [← hua, ← range_localNormFinite_eq_localNormSubgroup Q q hq]
  exact MonoidHom.mem_range.mpr ⟨u, rfl⟩

/-- The `ofFinite Q`-component of the prime idèle at `Q`. -/
@[simp] theorem ideleOfPrime_apply_ofFinite_self (Q : HeightOneSpectrum (𝓞 K)) :
    (NK.HeckeL.ideleOfPrime K Q) (Place.ofFinite Q) = IdeleClassGroup.unifUnit K Q := by
  classical
  rw [NK.HeckeL.ideleOfPrime]
  change IdeleClassGroup.unifUnit K Q ^ (if Q = Q then (1 : ℤ) else 0) =
    IdeleClassGroup.unifUnit K Q
  rw [if_pos rfl, zpow_one]

/-- The `ofFinite q`-component of the prime idèle at `Q ≠ q`. -/
theorem ideleOfPrime_apply_ofFinite_ne_exists {q Q : HeightOneSpectrum (𝓞 K)} (h : q ≠ Q) :
    (NK.HeckeL.ideleOfPrime K Q) (Place.ofFinite q) = 1 := by
  classical
  rw [NK.HeckeL.ideleOfPrime]
  change IdeleClassGroup.unifUnit K q ^ (if q = Q then (1 : ℤ) else 0) = 1
  rw [if_neg h, zpow_zero]

/-- The archimedean components of a prime idèle are trivial. -/
@[simp] theorem ideleOfPrime_apply_ofInfinite (Q : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    (NK.HeckeL.ideleOfPrime K Q) (Place.ofInfinite w) = 1 := rfl

/-! ## The local–global Artin map -/

theorem exists_localGlobalArtinMap_aux (hcyc : IsCyclic (L ≃ₐ[K] L))
    (hw : ∀ w : InfinitePlace K, ∃ F : (w.Completion)ˣ →* (L ≃ₐ[K] L),
      MonoidHom.ker F = localNormSubgroup (K := K) (L := L) (Place.ofInfinite w)) :
    ∃ Φ : Idele K →* (L ≃ₐ[K] L), Function.Surjective Φ ∧
      (∀ y : Idele L, Φ (Idele.normIdeleHom K L y) = 1) ∧
      (∀ (v : Place K) (a : (Place.localField K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          NK.HassePrinciple.onePlace v a ∈ Idele.normImage K L) ∧
      (∀ (Q : HeightOneSpectrum (𝓞 K)), NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  haveI : IsCyclic (L ≃ₐ[K] L) := hcyc
  have hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  let Ffin : (Q : HeightOneSpectrum (𝓞 K)) → (Q.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    fun Q => Classical.choose (exists_localMap_ofFinite (K := K) (L := L) hcyc Q)
  have hFfin_ker : ∀ Q, MonoidHom.ker (Ffin Q) =
      localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) :=
    fun Q => (Classical.choose_spec (exists_localMap_ofFinite (K := K) (L := L) hcyc Q)).1
  have hFfin_unif : ∀ (Q : HeightOneSpectrum (𝓞 K))
      (hu : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q),
      Ffin Q (IdeleClassGroup.unifUnit K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q :=
    fun Q hu => (Classical.choose_spec (exists_localMap_ofFinite (K := K) (L := L) hcyc Q)).2 hu
  let Finf : (w : InfinitePlace K) → (w.Completion)ˣ →* (L ≃ₐ[K] L) :=
    fun w => Classical.choose (hw w)
  have hFinf_ker : ∀ w, MonoidHom.ker (Finf w) =
      localNormSubgroup (K := K) (L := L) (Place.ofInfinite w) :=
    fun w => Classical.choose_spec (hw w)
  let F : ∀ v : Place K, (Place.localField K v)ˣ →* (L ≃ₐ[K] L) := fun v =>
    match v with
    | Sum.inl w => Finf w
    | Sum.inr Q => Ffin Q
  have hF_ker : ∀ v : Place K, MonoidHom.ker (F v) =
      localNormSubgroup (K := K) (L := L) v := by
    intro v; cases v with
    | inl w => exact hFinf_ker w
    | inr Q => exact hFfin_ker Q
  have hF_ker_apply : ∀ (v : Place K) (a : (Place.localField K v)ˣ), F v a = 1 ↔
      a ∈ localNormSubgroup (K := K) (L := L) v := by
    intro v a
    rw [← MonoidHom.mem_ker, hF_ker v]
  have hsupport : ∀ y : Idele K, {v : Place K | F v (y v) ≠ 1}.Finite := by
    intro y
    have hInf : ({v : Place K | Place.IsInfinite v} : Set (Place K)).Finite := by
      refine (Finset.finite_toSet (Finset.univ.image (Place.ofInfinite (K := K)))).subset ?_
      intro v hv
      obtain ⟨w, rfl⟩ := Place.isInfinite_iff.mp hv
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ w))
    have hNu : ({v : Place K | y v ∉ Place.localUnits K v} : Set (Place K)).Finite :=
      Filter.eventually_cofinite.mp y.2
    have hRam : ({v : Place K | ∃ q : HeightOneSpectrum (𝓞 L),
        q.asIdeal.ramificationIdx (𝓞 K) ≠ 1 ∧
          NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L (Place.ofFinite q) = v}
        : Set (Place K)).Finite := by
      have hq := Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K)
        (L := L)
      refine (hq.image (fun q : HeightOneSpectrum (𝓞 L) =>
        NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L (Place.ofFinite q))).subset ?_
      rintro v ⟨q, hqe, hqeq⟩
      exact ⟨q, hqe, hqeq⟩
    refine Set.Finite.subset (hInf.union (hNu.union hRam)) ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hnot
    push_neg at hnot
    obtain ⟨h1, h2, h3⟩ := hnot
    obtain ⟨Q, rfl⟩ := Place.isFinite_iff.mp h1
    have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q := by
      intro q hq
      by_contra hqe
      exact h3 q hqe
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_eq_of_liesOver
          (Place.liesOver_ofFinite hq))
    exact hv ((hF_ker_apply (Place.ofFinite Q) (y (Place.ofFinite Q))).mpr
      (localUnits_le_localNormSubgroup_of_unramified (K := K) (L := L) Q hunr h2))
  let Φ : Idele K →* (L ≃ₐ[K] L) := ideleHomOfLocal hcomm F hsupport
  have hΦ : ∀ y : Idele K, Φ y = cprod hcomm (hsupport y).toFinset (fun v => F v (y v)) := by
    intro y
    dsimp only [Φ]
    rw [ideleHomOfLocal_apply]
  have hΦ_onePlace : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = F v a := by
    intro v a
    exact ideleHomOfLocal_apply_onePlace hcomm F hsupport v a
  have h4 : ∀ (Q : HeightOneSpectrum (𝓞 K)),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
    intro Q hunr
    rw [hΦ]
    have hsingle := cprod_eq_single (hcomm := hcomm)
      (s := (hsupport (NK.HeckeL.ideleOfPrime K Q)).toFinset)
      (f := fun v => F v ((NK.HeckeL.ideleOfPrime K Q) v)) (Place.ofFinite Q)
      (fun b _ hb => by
        cases b with
        | inl w => rw [ideleOfPrime_apply_ofInfinite, map_one]
        | inr q =>
            have hqQ : q ≠ Q := fun h => hb (by rw [h])
            rw [ideleOfPrime_apply_ofFinite_ne_exists hqQ, map_one])
      (fun hv => by
        by_contra h
        exact hv ((Set.Finite.mem_toFinset _).mpr h))
    rw [hsingle, ideleOfPrime_apply_ofFinite_self]
    exact hFfin_unif Q hunr
  have h1 : ∀ y : Idele L, Φ (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hΦ]
    refine cprod_eq_one hcomm fun v _ => ?_
    rw [Idele.normIdeleHom_apply]
    exact (hF_ker_apply v _).mpr (normIdeleFun_mem_localNormSubgroup (K := K) (L := L) y v)
  have h3' : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
        NK.HassePrinciple.onePlace v a ∈ Idele.normImage K L := by
    intro v a
    rw [hΦ_onePlace v a, hF_ker_apply v a]
    exact (onePlace_mem_normImage_iff (K := K) (L := L) v a).symm
  have h2 : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top]
    let T : Finset (HeightOneSpectrum (𝓞 K)) :=
      ((Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K)
        (L := L)).toFinset.image (fun q : HeightOneSpectrum (𝓞 L) =>
          HeightOneSpectrum.under (𝓞 K) q))
    refine NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem (K := K) (L := L) T
      Φ.range ?_
    intro p hp σ hσ
    have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
      intro q hq
      by_contra hqe
      have hmem : p ∈ T := by
        refine Finset.mem_image.mpr ⟨q, ?_, ?_⟩
        · rw [Set.Finite.mem_toFinset]; exact hqe
        · exact HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, hq.over])
      exact hp hmem
    rw [NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcomm p hunr σ] at hσ
    exact ⟨NK.HeckeL.ideleOfPrime K p, by rw [h4 p hunr, hσ]⟩
  exact ⟨Φ, h2, h1, h3', h4⟩


/-! ## The archimedean local Artin map

The construction of the local–global Artin map `∏_v λ_v` needs a local map `λ_v` at every place
`v` of `K`, with kernel the local norm subgroup.  At a finite place this is
`exists_localMap_ofFinite`; at an infinite place the local field is `ℝ` or `ℂ` and the map is
either trivial (the local norm is surjective) or the sign character onto an involution of
`Gal(L/K)`.  This section supplies the archimedean case. -/

open scoped NumberField.LiesOver

section InfiniteLocalMap

/-- **A lift of an archimedean place to a finite extension.**  Every infinite place `v` of `K`
has a place of `L` above it. -/
theorem exists_liesOver_infinite (v : InfinitePlace K) :
    ∃ w : InfinitePlace L, w.LiesOver v := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  refine ⟨w, AbsoluteValue.LiesOver.mk ?_⟩
  have hh : (w.comap (algebraMap K L)).1 = v.1 := congrArg Subtype.val hw
  rw [← hh]
  rfl

/-- **The Galois action preserves the archimedean type.**  If `w₀` is a complex place of `L` above
`v`, then so is every place of `L` above `v` (the action of `Gal(L/K)` on the places above `v` is
transitive and commutes with complex conjugation). -/
theorem all_isComplex_of_isComplex {v : InfinitePlace K} {w₀ : InfinitePlace L} (h₀ : w₀.LiesOver v)
    (hw₀ : w₀.IsComplex) : ∀ w' : InfinitePlace L, w'.LiesOver v → w'.IsComplex := by
  intro w' hw'
  obtain ⟨σ, hσ⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
    (Place.liesOver_ofInfinite h₀) (Place.liesOver_ofInfinite hw')
  rw [Place.smul_ofInfinite, Place.ofInfinite_inj] at hσ
  rw [← hσ]
  exact InfinitePlace.isComplex_smul_iff.mpr hw₀

/-- **The archimedean local norm subgroup in the ramified case.**  If `v` is a real place and `w₀`
a complex place of `L` above it, then the local norm subgroup of `K_vˣ = ℝˣ` is the subgroup of
positive units: the local norm `ℂˣ → ℝˣ`, `z ↦ z z̄ = |z|²`, has image `ℝ_{>0}`, and all the local
norms `N_{L_{w'}/K_v}` over `w' | v` have the same image. -/
theorem localNormSubgroup_eq_posSubgroup_comap {v : InfinitePlace K} {w₀ : InfinitePlace L}
    (h₀ : w₀.LiesOver v) (hvR : v.IsReal) (hw₀C : w₀.IsComplex) :
    localNormSubgroup (K:=K) (L:=L) (Place.ofInfinite v)
      = (Units.posSubgroup ℝ).comap
          (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom
            : (v.Completion)ˣ →* ℝˣ) := by
  have hAllC := all_isComplex_of_isComplex h₀ hw₀C
  refine le_antisymm (iSup_le fun w' => ?_) ?_
  · rintro - ⟨y, rfl⟩
    haveI : w'.1.LiesOver v := w'.2
    rw [Subgroup.mem_comap, Units.mem_posSubgroup]
    rw [show Place.localNormInfinite w'.1 v
        = Units.map (Algebra.norm v.Completion : w'.1.Completion →* v.Completion) from rfl]
    simp only [Units.coe_map]
    have hcomp := NK.NUV2.ArtinBridge.localNormInfinite_norm_eq_real_complex
      (v := v) (w := w'.1) hvR (hAllC w'.1 w'.2) (y : w'.1.Completion)
    change 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
      ((Algebra.norm v.Completion) (y : w'.1.Completion))
    rw [hcomp]
    exact Complex.normSq_pos.mpr (fun h => y.ne_zero
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (hAllC w'.1 w'.2)).injective
        (by rw [h, map_zero])))
  · rw [localNormSubgroup_ofInfinite]
    have hle := NK.NUV2.ArtinBridge.localNormInfinite_posSubgroup_le_range_of_real_complex
      (v := v) (w := w₀) (hw := h₀) hvR hw₀C
    refine hle.trans ?_
    exact le_iSup (fun w' : {w' : InfinitePlace L // w'.LiesOver v} =>
      MonoidHom.range (@Place.localNormInfinite K _ L _ _ w'.1 v w'.2)) ⟨w₀, h₀⟩

/-- The local norm subgroup at an infinite place is everything as soon as one single local norm is
surjective, because it is the supremum of the local norm images. -/
theorem localNormSubgroup_eq_top_of_range_top {v : InfinitePlace K} {w₀ : InfinitePlace L}
    [hw : w₀.LiesOver v] (hrange : MonoidHom.range (Place.localNormInfinite w₀ v) = ⊤) :
    localNormSubgroup (K:=K) (L:=L) (Place.ofInfinite v) = ⊤ := by
  refine top_le_iff.mp ?_
  have h : MonoidHom.range (@Place.localNormInfinite K _ L _ _ w₀ v hw) ≤
      localNormSubgroup (K := K) (L := L) (Place.ofInfinite v) := by
    rw [localNormSubgroup_ofInfinite]
    exact le_iSup (fun w' : {w' : InfinitePlace L // w'.LiesOver v} =>
      MonoidHom.range (@Place.localNormInfinite K _ L _ _ w'.1 v w'.2)) ⟨w₀, hw⟩
  rw [hrange] at h
  exact h

/-- **An involution of `Gal(L/K)` at a ramified archimedean place.**  If `v` is a real place of `K`
and `w₀` a complex place of `L` above it, then there is a nontrivial involution of `L` over `K`:
the local Galois group of `ℂ/ℝ` is `ℤ/2`, and complex conjugation on the embedding `w₀` is a
`K`-automorphism. -/
theorem exists_involution_of_real_complex {v : InfinitePlace K} {w₀ : InfinitePlace L}
    (h₀ : w₀.LiesOver v) (hvR : v.IsReal) (hw₀C : w₀.IsComplex) :
    ∃ τ : L ≃ₐ[K] L, τ ≠ 1 ∧ τ * τ = 1 := by
  haveI : w₀.LiesOver v := h₀
  obtain ⟨σ, -, hσemb⟩ := NK.GlobalCFT.Galois.exists_conj_aut (K := K) (L := L) hw₀C hvR
  have hconj_ne : star w₀.embedding ≠ w₀.embedding := by
    intro h
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr hw₀C)
      ((InfinitePlace.isReal_iff (w := w₀)).mpr (ComplexEmbedding.isReal_iff.mpr h))
  obtain ⟨x, hx⟩ : ∃ x : L, (starRingEnd ℂ) (w₀.embedding x) ≠ w₀.embedding x := by
    by_contra h
    push_neg at h
    exact hconj_ne (RingHom.ext fun y => by
      simpa [ComplexEmbedding.conjugate, RingHom.star_apply] using h y)
  refine ⟨σ, ?_, ?_⟩
  · intro h
    exact hx (by rw [← hσemb x, h, AlgEquiv.one_apply])
  · ext y
    apply w₀.embedding.injective
    rw [AlgEquiv.mul_apply, hσemb (σ y), hσemb y]
    exact Complex.conj_conj _

/-- **The local Artin map at an archimedean place.**  Together with `exists_localMap_ofFinite` this
is the complete set of local factors of the local–global Artin map: for every place `v` of `K`
there is a homomorphism `K_vˣ →* Gal(L/K)` whose kernel is the local norm subgroup.

At an infinite place `K_v` is `ℝ` or `ℂ`, so `K_vˣ` is `ℝˣ` or `ℂˣ` and the local norm subgroup is
either everything (the extensions `ℝ/ℝ`, `ℂ/ℂ`) or the group `ℝ_{>0}` of positive units
(`ℂ/ℝ`, where the norm is `z ↦ |z|²`).  The map is then trivial in the first case and the sign
character onto a nontrivial involution of `Gal(L/K)` in the second. -/
theorem exists_localMap_ofInfinite_noCyc (v : InfinitePlace K) :
    ∃ F : (v.Completion)ˣ →* (L ≃ₐ[K] L),
      MonoidHom.ker F = localNormSubgroup (K := K) (L := L) (Place.ofInfinite v) := by
  classical
  obtain ⟨w₀, hw₀⟩ := exists_liesOver_infinite (K := K) (L := L) v
  haveI : w₀.LiesOver v := hw₀
  by_cases hvR : v.IsReal
  · by_cases hw₀R : w₀.IsReal
    · -- the local extension `ℝ/ℝ` is trivial: the local norm is surjective
      have hrange : MonoidHom.range (Place.localNormInfinite w₀ v) = ⊤ := by
        rw [show Place.localNormInfinite w₀ v
            = Units.map (Algebra.norm v.Completion : w₀.Completion →* v.Completion) from rfl]
        exact NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_real_real hvR hw₀R
      refine ⟨1, ?_⟩
      rw [MonoidHom.ker_one]
      exact (localNormSubgroup_eq_top_of_range_top hrange).symm
    · -- the local extension is `ℂ/ℝ`: the sign character
      have hw₀C : w₀.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw₀R
      obtain ⟨τ, hτ1, hτ2⟩ := exists_involution_of_real_complex hw₀ hvR hw₀C
      let sign : ℝˣ →* (L ≃ₐ[K] L) :=
        { toFun := fun x => if 0 < (x : ℝ) then 1 else τ
          map_one' := by rw [if_pos (show (0 : ℝ) < ((1 : ℝˣ) : ℝ) by norm_num)]
          map_mul' := by
            intro x y
            rw [Units.val_mul]
            rcases lt_trichotomy (0 : ℝ) (x : ℝ) with hx | hx | hx
            · rcases lt_trichotomy (0 : ℝ) (y : ℝ) with hy | hy | hy
              · rw [if_pos hx, if_pos hy, if_pos (mul_pos hx hy), one_mul]
              · exact absurd hy.symm (Units.ne_zero y)
              · rw [if_pos hx, if_neg (not_lt.mpr hy.le),
                  if_neg (not_lt.mpr (le_of_lt (mul_neg_of_pos_of_neg hx hy))), one_mul]
            · exact absurd hx.symm (Units.ne_zero x)
            · rcases lt_trichotomy (0 : ℝ) (y : ℝ) with hy | hy | hy
              · rw [if_neg (not_lt.mpr hx.le), if_pos hy,
                  if_neg (not_lt.mpr (le_of_lt (mul_neg_of_neg_of_pos hx hy))), mul_one]
              · exact absurd hy.symm (Units.ne_zero y)
              · rw [if_neg (not_lt.mpr hx.le), if_neg (not_lt.mpr hy.le),
                  if_pos (mul_pos_of_neg_of_neg hx hy), hτ2] }
      have hker_sign : MonoidHom.ker sign = Units.posSubgroup ℝ := by
        ext x
        rw [MonoidHom.mem_ker, Units.mem_posSubgroup]
        change (if 0 < (x : ℝ) then 1 else τ) = 1 ↔ 0 < (x : ℝ)
        by_cases hx : 0 < (x : ℝ)
        · rw [if_pos hx]; exact ⟨fun _ => hx, fun _ => rfl⟩
        · rw [if_neg hx]; exact ⟨fun h => absurd h hτ1, fun h => absurd h hx⟩
      refine ⟨sign.comp (Units.map
        (InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom), ?_⟩
      rw [localNormSubgroup_eq_posSubgroup_comap hw₀ hvR hw₀C]
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hker_sign, Subgroup.mem_comap,
        MonoidHom.mem_ker]
  · -- the local extension `ℂ/ℂ` is trivial: the local norm is surjective
    have hvC : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hvR
    have hw₀C : w₀.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under w₀ hvC
    have hrange : MonoidHom.range (Place.localNormInfinite w₀ v) = ⊤ := by
      rw [show Place.localNormInfinite w₀ v
          = Units.map (Algebra.norm v.Completion : w₀.Completion →* v.Completion) from rfl]
      exact NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex hvC hw₀C
    refine ⟨1, ?_⟩
    rw [MonoidHom.ker_one]
    exact (localNormSubgroup_eq_top_of_range_top hrange).symm

end InfiniteLocalMap

/-- **The canonical local–global Artin map** (Milne, *CFT*, V.5.2/V.5.3): the product `∏_v θ_v`
of the local Artin maps of a cyclic extension `L/K` of number fields.

There is a surjective homomorphism `Φ : 𝕀 K →* Gal(L/K)` with

* `Φ` kills the idèle norms `N_{L/K}𝕀_L`;
* `Φ` is one-place faithful: `Φ (onePlace v a) = 1 ↔ onePlace v a ∈ N_{L/K}𝕀_L` (equivalently, by
  the local–global principle, iff `a` is a local norm at `v`);
* `Φ` is Frobenius-normalised: `Φ (ideleOfPrime K Q) = frobAtPrime Q` for every `Q` unramified in
  `L/K`.

This is the `Φ` for which the reciprocity law takes the form of *Hilbert reciprocity*,
"`Φ` kills `Kˣ`" (Milne VII.8.1(a)); it is the same statement as the existing sorry'd
`NK.CFTLib.IdeleHasse.exists_localGlobalArtinMap` (whose docstring records the full route), so a
proof here can simply be transplanted.

Construction (**no new arithmetic, only gluing**):

* **Finite places.**  For `Q` finite and `q | Q`, the local Artin map
  `λ_Q : (Q.adicCompletion K)ˣ →* Gal(q.adicCompletion L / Q.adicCompletion K)` is the standard
  local Artin map, surjective with kernel the local norm group:
  `Commons.NumberTheory.NumberField.Completion.exists_artinMap_of_abelian_local`
  (the local Galois group is the decomposition subgroup of the abelian `Gal(L/K)`, hence
  commutative — the cyclic hypothesis `hcyc` supplies commutativity).  Compose with the
  identification of that local Galois group with the decomposition subgroup of `Gal(L/K)`
  (`Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois`, or
  `NK.GlobalCFTdeep.Herbrand.decompositionSubgroupIsoLocalGalois_apply`) and the inclusion into
  `Gal(L/K)`.
* **Infinite places.**  `Place.localField K v` is `ℝ` or `ℂ`; the extension is `ℝ/ℝ`, `ℂ/ℂ` (norm
  surjective on `ℝˣ`/`ℂˣ`, take the trivial map) or `ℂ/ℝ` (norm is `z ↦ |z|²` with image
  `ℝ_{>0}`, take the sign character `ℝˣ → Gal(ℂ/ℝ) ≅ ℤ/2`).
* **Gluing.**  Fix one `w | v` for each `v` and set `Φ(y) := ∏_v λ_v(y_v)`; the product is finite
  because `λ_v` vanishes on the units of almost every `v` (a unit is a norm when
  `ramificationIdx = 1`, `NK.NUV2.ARL.localUnits_le_imageLocalNormFinite_of_ramificationIdx_eq_one`),
  and it is independent of the choices `w | v` because `Gal(L/K)` is abelian.
* **Kernel clause.**  `ker λ_v = N_v`, so `Φ (onePlace v a) = 1 ↔ a ∈ N_v`; combine with the
  one-place dictionary `NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff` (or
  `mem_normImage_iff_localNorm`: all components of `onePlace v a` other than `v` are `1`, which is
  a norm).
* **Surjectivity.**  The Frobenius elements at the unramified primes generate `Gal(L/K)`
  (Chebotarev / Frobenius generation).
* **Frobenius clause.**  For unramified `Q` the local Artin map sends the uniformiser idèle to a
  Frobenius element, and at an unramified prime of an abelian extension the Frobenius element is
  unique (`NK.Chebotarev.ExistsUniqueIsFrobAtPrime`), so it equals `frobAtPrime Q`.  The proven
  `NK.CFTLib.Arl.frobAtPrime_eq_ideleArtin_of_isUnramified` is the same normalisation.

The proof below follows the gluing route: `exists_localGlobalArtinMap_aux` assembles the glued map
from the local factors and proves the four clauses, and `exists_localMap_ofFinite` (finite places)
and `exists_localMap_ofInfinite` (archimedean places) supply the local factors with the required
kernels.  Nothing here uses the idèlic reciprocity law or Hilbert reciprocity; the only global
input is the Frobenius generation theorem (Chebotarev/Dedekind density) inside
`NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem`. -/
theorem localGlobalArtinMap_exists
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L)) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L), Function.Surjective Φ ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      (∀ (v : NK.GlobalCFT.Place K) (a : (NK.GlobalCFT.Place.localField K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L) ∧
      (∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q)
          = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) :=
  exists_localGlobalArtinMap_aux hcyc fun w => exists_localMap_ofInfinite_noCyc w

end NK.CFTLib.IdeleHasse

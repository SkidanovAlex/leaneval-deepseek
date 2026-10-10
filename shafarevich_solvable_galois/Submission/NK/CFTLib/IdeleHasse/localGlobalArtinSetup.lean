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
import Submission.NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormInfinite_range
import Submission.NK.NUV2.ArtinBridge.localUnits_le_image_localNormFinite_of_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local–global Artin map `Φ = ∏_v λ_v`

This module assembles the local–global Artin map of a finite extension `L / K` of number fields as
the finite product of its local factors:

* the local factors at the finite places are supplied by `exists_localMap_ofFinite` (the local
  Artin map of local class field theory, Frobenius-normalised at unramified primes);
* the archimedean factors are constructed here (`exists_localMap_ofInfinite`): the trivial map when
  the local norm is onto, the sign character when `K_w = ℝ` and every place of `L` above `w` is
  complex;
* the gluing of the local factors into a single homomorphism `𝕀[K] →* Gal(L/K)` is
  `NK.CFTLib.IdeleHasse.ideleHomOfLocal` (a finite product, well defined because an idèle is a
  local unit at all but finitely many places).

The main result is `NK.CFTLib.IdeleHasse.exists_localGlobalArtinMap'`, the four clauses
(norm-killing, surjectivity, one-place faithfulness, Frobenius normalisation) that make `Φ` the
canonical local–global Artin map.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped NumberField NumberField.LiesOver RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.IdeleHasse

open NK.GlobalCFT


open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- In the archimedean real/complex case the range of the local norm is the subgroup of positive
reals. -/
theorem range_localNormInfinite_of_real_complex {w : InfinitePlace K} {w' : InfinitePlace L}
    [hw' : w'.LiesOver w] (hvR : w.IsReal) (hwC : w'.IsComplex) :
    (Place.localNormInfinite w' w).range =
      (Units.posSubgroup ℝ).comap (Units.map
        (InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom) := by
  refine le_antisymm ?_ ?_
  · rintro u ⟨z, rfl⟩
    rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
    change 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
      (Algebra.norm w.Completion (z : w'.Completion))
    rw [NK.NUV2.ArtinBridge.localNormInfinite_norm_eq_real_complex hvR hwC (z : w'.Completion)]
    exact Complex.normSq_pos.mpr (fun h => z.ne_zero
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).injective
        (by rw [h, map_zero])))
  · intro u hu
    rw [Subgroup.mem_comap] at hu
    exact NK.NUV2.ArtinBridge.localNormInfinite_posSubgroup_le_range_of_real_complex hvR hwC hu

/-- **The archimedean local factor of the local–global Artin map.**  For an infinite place `w`
of `K` there is a homomorphism `K_wˣ →* Gal(L/K)` whose kernel is the local norm subgroup:
the trivial map when the local norm is onto (`K_w = ℂ`, or `K_w = ℝ` with a real place of `L`
above it), and the sign character when `K_w = ℝ` and every place of `L` above `w` is complex. -/
theorem exists_localMap_ofInfinite (hcyc : IsCyclic (L ≃ₐ[K] L)) (w : InfinitePlace K) :
    ∃ F : (w.Completion)ˣ →* (L ≃ₐ[K] L),
      MonoidHom.ker F = localNormSubgroup (K := K) (L := L) (Place.ofInfinite w) := by
  classical
  let w₀ : InfinitePlace L := Classical.choose (InfinitePlace.comap_surjective (k := K) (K := L) w)
  have hw₀ : w₀.LiesOver w := (Norm.liesOver_iff_comap_eq w₀ w).mpr
    (Classical.choose_spec (InfinitePlace.comap_surjective (k := K) (K := L) w))
  haveI : w₀.LiesOver w := hw₀
  by_cases hwc : w.IsComplex
  · -- `K_w = ℂ`: the local norm is onto
    refine ⟨1, ?_⟩
    rw [MonoidHom.ker_one]
    refine le_antisymm ?_ le_top
    rw [localNormSubgroup_ofInfinite (K := K) (L := L)]
    refine le_trans (le_of_eq ?_) (le_iSup_of_le ⟨w₀, hw₀⟩ le_rfl)
    exact (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex
      (v := w) (w := w₀) hwc (InfinitePlace.LiesOver.isComplex_of_isComplex_under w₀ hwc)).symm
  · have hwR : w.IsReal := InfinitePlace.not_isComplex_iff_isReal.mp hwc
    by_cases hre : ∃ w' : InfinitePlace L, w'.LiesOver w ∧ w'.IsReal
    · -- a real place above a real place: the local norm is onto
      obtain ⟨w₁, hw₁, hw₁R⟩ := hre
      refine ⟨1, ?_⟩
      rw [MonoidHom.ker_one]
      refine le_antisymm ?_ le_top
      rw [localNormSubgroup_ofInfinite (K := K) (L := L)]
      refine le_trans (le_of_eq ?_) (le_iSup_of_le ⟨w₁, hw₁⟩ le_rfl)
      exact (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_real_real
        (v := w) (w := w₁) hwR hw₁R).symm
    · -- every place of `L` above `w` is complex: the local norm is the positive reals
      have hcomp : ∀ (w' : InfinitePlace L) (h : w'.LiesOver w), w'.IsComplex :=
        fun w' h => InfinitePlace.not_isReal_iff_isComplex.mp fun hR => hre ⟨w', h, hR⟩
      -- an element of order two
      have hstab : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w₀) = 2 := by
        refine NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.mp ?_
        rw [NumberField.InfinitePlace.isUnramified_iff]
        refine not_or.mpr ⟨?_, ?_⟩
        · exact fun hR => InfinitePlace.not_isReal_iff_isComplex.mpr (hcomp w₀ hw₀) hR
        · rw [InfinitePlace.LiesOver.comap_eq w₀ w]
          exact InfinitePlace.not_isComplex_iff_isReal.mpr hwR
      have hcard : Fintype.card ↥(MulAction.stabilizer (L ≃ₐ[K] L) w₀) = 2 := by
        rw [← Nat.card_eq_fintype_card]; exact hstab
      obtain ⟨x, hx⟩ : ∃ x : ↥(MulAction.stabilizer (L ≃ₐ[K] L) w₀), x ≠ 1 :=
        Fintype.exists_ne_of_one_lt_card (by rw [hcard]; norm_num)
          (1 : ↥(MulAction.stabilizer (L ≃ₐ[K] L) w₀))
      have hx2 : x ^ 2 = 1 := by
        have hdiv : orderOf x ∣ 2 := by
          have := orderOf_dvd_natCard x
          rwa [hstab] at this
        have hne : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
        rw [← pow_orderOf_eq_one x]
        congr 1
        rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
        · exact absurd h hne
        · exact h.symm
      set σ : L ≃ₐ[K] L := (x : L ≃ₐ[K] L) with hσdef
      have hσne : σ ≠ 1 := fun h => hx (Subtype.ext h)
      have hσ2 : σ * σ = 1 := by
        have h := congrArg (fun y : ↥(MulAction.stabilizer (L ≃ₐ[K] L) w₀) => (y : L ≃ₐ[K] L)) hx2
        simpa [hσdef, pow_two] using h
      -- the sign character
      have hsgn : ∀ a : ℝˣ, (if 0 < (a : ℝ) then (1 : L ≃ₐ[K] L) else σ) = 1 ↔ 0 < (a : ℝ) := by
        intro a
        by_cases ha : 0 < (a : ℝ)
        · rw [if_pos ha]; exact ⟨fun _ => ha, fun _ => rfl⟩
        · have ha' : (a : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp ha) (Units.ne_zero a)
          rw [if_neg ha]
          exact ⟨fun h => absurd h hσne, fun h => absurd h (not_lt.mpr ha'.le)⟩
      have hmul : ∀ a b : ℝˣ, (if 0 < ((a * b : ℝˣ) : ℝ) then (1 : L ≃ₐ[K] L) else σ)
          = (if 0 < (a : ℝ) then 1 else σ) * (if 0 < (b : ℝ) then 1 else σ) := by
        intro a b
        have ha : (a : ℝ) < 0 ∨ 0 < (a : ℝ) :=
          lt_or_gt_of_ne (a := (a : ℝ)) (b := 0) (Units.ne_zero a)
        have hb : (b : ℝ) < 0 ∨ 0 < (b : ℝ) :=
          lt_or_gt_of_ne (a := (b : ℝ)) (b := 0) (Units.ne_zero b)
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · rw [Units.val_mul, if_pos (mul_pos_of_neg_of_neg ha hb),
            if_neg (not_lt.mpr ha.le), if_neg (not_lt.mpr hb.le), hσ2]
        · rw [Units.val_mul, if_neg (not_lt.mpr (mul_neg_of_neg_of_pos ha hb).le),
            if_neg (not_lt.mpr ha.le), if_pos hb, mul_one]
        · rw [Units.val_mul, if_neg (not_lt.mpr (mul_neg_of_pos_of_neg ha hb).le),
            if_pos ha, if_neg (not_lt.mpr hb.le), one_mul]
        · rw [Units.val_mul, if_pos (mul_pos ha hb), if_pos ha, if_pos hb, mul_one]
      let sgn : ℝˣ →* (L ≃ₐ[K] L) :=
        { toFun := fun a => if 0 < (a : ℝ) then 1 else σ
          map_one' := by simp
          map_mul' := hmul }
      have hker_sgn : MonoidHom.ker sgn = Units.posSubgroup ℝ := by
        ext a
        rw [MonoidHom.mem_ker, Units.mem_posSubgroup]
        change (if 0 < (a : ℝ) then (1 : L ≃ₐ[K] L) else σ) = 1 ↔ 0 < (a : ℝ)
        exact hsgn a
      -- the subgroup of local norms is the subgroup of positive reals
      have hsub : localNormSubgroup (K := K) (L := L) (Place.ofInfinite w)
          = (Units.posSubgroup ℝ).comap (Units.map
              (InfinitePlace.Completion.ringEquivRealOfIsReal hwR).toMulEquiv.toMonoidHom) := by
        rw [localNormSubgroup_ofInfinite (K := K) (L := L)]
        refine le_antisymm (iSup_le fun w' => ?_) ?_
        · rw [range_localNormInfinite_of_real_complex (w := w) (w' := w'.1) (hw' := w'.2) hwR
            (hcomp w'.1 w'.2)]
        · exact le_iSup_of_le ⟨w₀, hw₀⟩ (le_of_eq (range_localNormInfinite_of_real_complex
            (w := w) (w' := w₀) (hw' := hw₀) hwR (hcomp w₀ hw₀)).symm)
      refine ⟨sgn.comp (Units.map
        (InfinitePlace.Completion.ringEquivRealOfIsReal hwR).toMulEquiv.toMonoidHom), ?_⟩
      rw [hsub]
      ext a
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker (f := sgn), hker_sgn,
        Subgroup.mem_comap]




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
theorem ideleOfPrime_apply_ofFinite_ne_setup {q Q : HeightOneSpectrum (𝓞 K)} (h : q ≠ Q) :
    (NK.HeckeL.ideleOfPrime K Q) (Place.ofFinite q) = 1 := by
  classical
  rw [NK.HeckeL.ideleOfPrime]
  change IdeleClassGroup.unifUnit K q ^ (if q = Q then (1 : ℤ) else 0) = 1
  rw [if_neg h, zpow_zero]

/-- The archimedean components of a prime idèle are trivial. -/
@[simp] theorem ideleOfPrime_apply_ofInfinite (Q : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    (NK.HeckeL.ideleOfPrime K Q) (Place.ofInfinite w) = 1 := rfl

/-! ## The local–global Artin map -/

/-- **The local–global Artin map** `Φ = ∏_v λ_v`: the product of the local Artin maps, with

* `Φ` surjective and killing the idèle norms;
* `Φ` faithful on the one-place idèles: `Φ (onePlace v a) = 1` iff `a` is a local norm at `v`;
* `Φ` normalised by the Frobenius elements at the unramified primes. -/
theorem exists_localGlobalArtinMap' (hcyc : IsCyclic (L ≃ₐ[K] L)) :
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
    fun w => Classical.choose (exists_localMap_ofInfinite (K := K) (L := L) hcyc w)
  have hFinf_ker : ∀ w, MonoidHom.ker (Finf w) =
      localNormSubgroup (K := K) (L := L) (Place.ofInfinite w) :=
    fun w => Classical.choose_spec (exists_localMap_ofInfinite (K := K) (L := L) hcyc w)
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
            rw [ideleOfPrime_apply_ofFinite_ne_setup hqQ, map_one])
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



end NK.CFTLib.IdeleHasse

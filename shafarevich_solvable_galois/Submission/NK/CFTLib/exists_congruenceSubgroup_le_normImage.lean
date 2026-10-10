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
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A congruence subgroup contained in the idèlic norm group

Let `L / K` be a finite Galois extension of number fields.  This file proves that there is a
modulus `m > 0` and a *congruence subgroup* `U ≤ 𝕀[K]` — the idèles which are local units outside
the primes dividing `m`, are `≡ 1 mod m` at the primes dividing `m`, and are positive at every real
place — such that `U ≤ N_{L/K} 𝕀[L]`.

This is the standard "the norm group is open, of finite index, and contains a congruence subgroup"
statement used in the idèlic proof of class field theory (Neukirch–Schmidt–Wingberg, *Cohomology
of Number Fields*, Chapter XII, the input to the reconstruction of the local correspondence in
Neukirch–Uchida).  Only the local theory of the norm map is used, no local class field theory:

* **Nonarchimedean, unramified.**  If `q | Q` is unramified then the local norm
  `N_{L_q/K_Q}` maps the local units of `L_q` *onto* the local units of `K_Q`
  (`localNormFinite_units_surjective_of_ramificationIdx_eq_one`, from
  `norm_range_of_ramificationIdx_eq_one`).
* **Nonarchimedean, ramified.**  The local norm `N_{L_q/K_Q}` is *open at the origin*: there is a
  level `n > 0` such that every `z ≡ 1 mod 𝔪^n` is a norm.  This is the elementary Newton-iteration
  computation `exists_norm_eq_of_val_sub_one_le_aux` (second order expansion of the norm, whose
  derivative is the surjective trace) packaged as `exists_level_localNormFinite`.
* **Archimedean.**  At a real place the positive elements are norms (the norm is either an
  isomorphism `ℝ ≅ ℝ`, or `N z = |z|²` for `ℂ/ℝ`); at a complex place everything is a norm
  (`posAtReal_mem_range_localNormInfinite`).

The modulus is `m = ∏_{Q ramified} N(Q)^N` where `N` is the maximum of the local levels
(`exists_modulus`), so that

* every ramified prime divides `(m)`, whence a prime not dividing `m` is unramified, and
* at a ramified prime `Q | (m)` the congruence condition of level `m` is finer than the local
  level `levelOf Q`, so the component lies in the local norm group
  (`mem_range_localNormFinite_of_val_le_levelOf`, `val_natCast_le_exp_neg_of_mem_pow`).

The per-place local data is then assembled into a global norm by
`NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField RestrictedProduct WithZero NumberField.LiesOver
open NumberField IsDedekindDomain

namespace NK.CFTLib

open NK.GlobalCFT

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

namespace ExistsCongruence

/-! ## Choices of places of `L` above the places of `K` -/

/-- A chosen prime of `𝓞 L` above a prime of `𝓞 K`. -/
noncomputable def abovePrime (Q : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 L) :=
  Classical.choose
    (Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q)

theorem abovePrime_liesOver (Q : HeightOneSpectrum (𝓞 K)) :
    (abovePrime (K := K) (L := L) Q).asIdeal.LiesOver Q.asIdeal :=
  Classical.choose_spec
    (Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q)

/-- A chosen infinite place of `L` above an infinite place of `K`. -/
noncomputable def aboveInf (w : InfinitePlace K) : InfinitePlace L :=
  Classical.choose (InfinitePlace.comap_surjective (k := K) (K := L) w)

theorem aboveInf_liesOver (w : InfinitePlace K) : (aboveInf (K := K) (L := L) w).LiesOver w := by
  rw [Norm.liesOver_iff_comap_eq]
  exact Classical.choose_spec (InfinitePlace.comap_surjective (k := K) (K := L) w)

theorem placeAbove_ofFinite (Q : HeightOneSpectrum (𝓞 K)) :
    IdeleHasse.placeAbove (K := K) (L := L) (Place.ofFinite Q) =
      Place.ofFinite (abovePrime (K := K) (L := L) Q) := rfl

theorem placeAbove_ofInfinite (w : InfinitePlace K) :
    IdeleHasse.placeAbove (K := K) (L := L) (Place.ofInfinite w) =
      Place.ofInfinite (aboveInf (K := K) (L := L) w) := rfl

/-! ## The local norm contains a neighbourhood of `1` -/

/-- **The local norm is open at the origin.**  For a finite place `Q` of `K` and a place `q` of
`L` above it there is a level `n > 0` such that every unit `z` of `K_Q` which is `≡ 1` modulo the
`n`-th power of the maximal ideal is a norm from `L_qˣ`. -/
theorem exists_level_localNormFinite (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : (Q.adicCompletion K)ˣ,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((z : Q.adicCompletion K) - 1) ≤
        (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) →
      z ∈ (Place.localNormFinite q Q hq).range := by
  obtain ⟨D, u₀, hu₀, hu₀D⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_trace_eq_one_adicCompletion
      (K := K) (L := L) Q q hq
  refine ⟨2 * D + 2, by omega, ?_⟩
  intro z hz
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  obtain ⟨x, hx⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_norm_eq_of_val_sub_one_le_aux
      (K := K) (L := L) Q q hq D u₀ hu₀ hu₀D (z : Q.adicCompletion K) hz
  haveI : Module.Free (Q.adicCompletion K) (q.adicCompletion L) :=
    Module.Free.of_divisionRing _ _
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  have hxne : x ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hx
    exact Units.ne_zero z hx.symm
  refine MonoidHom.mem_range.mpr ⟨Units.mk0 x hxne, ?_⟩
  refine Units.ext ?_
  rw [show Place.localNormFinite q Q hq =
    Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)
      from rfl]
  rw [Units.coe_map, Units.val_mk0]
  exact hx

/-- The level of the local norm at a prime of `𝓞 K`, attached to the chosen prime of `𝓞 L`
above it. -/
noncomputable def levelOf (Q : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Classical.choose (exists_level_localNormFinite (K := K) (L := L) Q
    (abovePrime (K := K) (L := L) Q) (abovePrime_liesOver Q))

theorem levelOf_pos (Q : HeightOneSpectrum (𝓞 K)) : 0 < levelOf (K := K) (L := L) Q :=
  (Classical.choose_spec (exists_level_localNormFinite Q (abovePrime Q) (abovePrime_liesOver Q))).1

/-- Every unit congruent to `1` modulo `levelOf Q` is a local norm. -/
theorem mem_range_localNormFinite_of_val_le_levelOf (Q : HeightOneSpectrum (𝓞 K))
    (z : (Q.adicCompletion K)ˣ)
    (hz : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((z : Q.adicCompletion K) - 1) ≤
      (WithZero.exp (-((levelOf (K := K) (L := L) Q : ℕ) : ℤ)) :
        WithZero (Multiplicative ℤ))) :
    z ∈ (Place.localNormFinite (abovePrime (K := K) (L := L) Q) Q
      (abovePrime_liesOver Q)).range :=
  (Classical.choose_spec (exists_level_localNormFinite Q (abovePrime Q)
    (abovePrime_liesOver Q))).2 z hz

/-! ## The ramified primes and the modulus -/

/-- The finite set of primes of `𝓞 K` which ramify in `L`. -/
noncomputable def ramPrimes : Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact (Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
    (K := K) (L := L)).toFinset.image
    (fun q => HeightOneSpectrum.under (𝓞 K) q)

theorem mem_ramPrimes_of_ramificationIdx_ne_one {Q : HeightOneSpectrum (𝓞 K)}
    {q : HeightOneSpectrum (𝓞 L)} (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h : q.asIdeal.ramificationIdx (𝓞 K) ≠ 1) : Q ∈ ramPrimes (K := K) (L := L) := by
  classical
  refine Finset.mem_image.mpr ⟨q, ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset]
    exact h
  · exact HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, hq.over])

theorem ramificationIdx_eq_one_of_notMem_ramPrimes {Q : HeightOneSpectrum (𝓞 K)}
    (hQ : Q ∉ ramPrimes (K := K) (L := L)) {q : HeightOneSpectrum (𝓞 L)}
    (hq : q.asIdeal.LiesOver Q.asIdeal) : q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  by_contra h
  exact hQ (mem_ramPrimes_of_ramificationIdx_ne_one hq h)

/-- **The modulus.**  There is `m > 0` which is divisible, at every ramified prime `Q`, by the
`levelOf Q`-th power of `Q`. -/
theorem exists_modulus :
    ∃ m : ℕ, 0 < m ∧ ∀ Q : HeightOneSpectrum (𝓞 K), Q ∈ ramPrimes (K := K) (L := L) →
      (m : 𝓞 K) ∈ Q.asIdeal ^ levelOf (K := K) (L := L) Q := by
  classical
  refine ⟨∏ Q ∈ ramPrimes (K := K) (L := L),
      (Ideal.absNorm Q.asIdeal) ^ (ramPrimes (K := K) (L := L)).sup
        (levelOf (K := K) (L := L)), ?_, ?_⟩
  · refine Finset.prod_pos fun Q _ => pow_pos ?_ _
    exact Nat.pos_of_ne_zero fun h => Q.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  · intro Q hQ
    have hAN : (((Ideal.absNorm Q.asIdeal) ^
        (ramPrimes (K := K) (L := L)).sup (levelOf (K := K) (L := L)) : ℕ) : 𝓞 K)
        ∈ Q.asIdeal ^ (ramPrimes (K := K) (L := L)).sup (levelOf (K := K) (L := L)) := by
      rw [Nat.cast_pow]
      exact Ideal.pow_mem_pow (Ideal.absNorm_mem Q.asIdeal) _
    have hle : levelOf (K := K) (L := L) Q ≤
        (ramPrimes (K := K) (L := L)).sup (levelOf (K := K) (L := L)) := Finset.le_sup hQ
    rw [← Finset.prod_erase_mul (ramPrimes (K := K) (L := L))
      (fun Q => (Ideal.absNorm Q.asIdeal) ^ (ramPrimes (K := K) (L := L)).sup
        (levelOf (K := K) (L := L))) hQ]
    rw [Nat.cast_mul]
    refine Ideal.mul_mem_left (Q.asIdeal ^ levelOf (K := K) (L := L) Q) _ ?_
    exact Ideal.pow_le_pow_right hle hAN

/-! ## The unramified case -/

/-- At an unramified prime, every unit congruent to `1` modulo `(m)` is a local norm. -/
theorem mem_range_localNormFinite_of_congr (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) {m : ℕ} (hmem : (m : 𝓞 K) ∈ Q.asIdeal)
    {z : (Q.adicCompletion K)ˣ}
    (hz : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((z : Q.adicCompletion K) - 1) ≤
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : Q.adicCompletion K))) :
    z ∈ (Place.localNormFinite q Q hq).range := by
  have hmlt : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((m : ℕ) : Q.adicCompletion K)) < 1 := Arl.val_natCast_lt_one Q m hmem
  have hz1 : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((z : Q.adicCompletion K) - 1) < 1 := lt_of_le_of_lt hz hmlt
  have hzval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (z : Q.adicCompletion K) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left
      (v := Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := (1 : Q.adicCompletion K)) (y := (z : Q.adicCompletion K) - 1)
      (by rw [map_one]; exact hz1)
    rw [map_one, show (1 : Q.adicCompletion K) + ((z : Q.adicCompletion K) - 1) =
      (z : Q.adicCompletion K) from by ring] at h
    exact h
  have hmem' : z ∈ Place.localUnits K (Place.ofFinite Q) :=
    Place.mem_localUnits_ofFinite_iff_valued_eq_one.mpr hzval
  obtain ⟨u, _, hua⟩ :=
    NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
      Q q hq hunr z hmem'
  exact ⟨u, hua⟩

/-! ## The archimedean places -/

/-- At an infinite place, a positive element of `K_vˣ` is a local norm. -/
theorem posAtReal_mem_range_localNormInfinite {v : InfinitePlace K} {w : InfinitePlace L}
    [hw : w.LiesOver v] {u : v.Completionˣ} (hu : Arl.PosAtReal v u) :
    u ∈ (Place.localNormInfinite w v).range := by
  have hdef : (Place.localNormInfinite w v) =
      Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) := rfl
  rcases InfinitePlace.isReal_or_isComplex v with hvR | hvC
  · rcases InfinitePlace.isReal_or_isComplex w with hwR | hwC
    · rw [hdef, NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real hvR hwR]
      exact Subgroup.mem_top _
    · have hmem : u ∈ Subgroup.comap
          (Units.map ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom) :
            v.Completionˣ →* ℝˣ) (Units.posSubgroup ℝ) := by
        rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
        exact hu hvR
      have h := NK.GlobalCFTdeep.NormIndex.localNormInfinite_posSubgroup_le_range_of_real_complex
        (v := v) (w := w) hvR hwC hmem
      rwa [hdef]
  · have hwC : w.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
    rw [hdef, NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex hvC hwC]
    exact Subgroup.mem_top _

/-! ## The value of an integer at a finite place -/

/-- The value of the integer `m` in the completion at `Q` is bounded by `exp (-n)` as soon as
`m ∈ Q ^ n`. -/
theorem val_natCast_le_exp_neg_of_mem_pow (Q : HeightOneSpectrum (𝓞 K)) (m n : ℕ)
    (h : ((m : ℕ) : 𝓞 K) ∈ Q.asIdeal ^ n) :
    Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : Q.adicCompletion K)) ≤
      (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
  have h1 : (((m : ℕ) : Q.adicCompletion K)) =
      algebraMap K (Q.adicCompletion K) ((m : K)) := (map_natCast _ m).symm
  rw [h1, Commons.NumberTheory.NumberField.Completion.valued_alg_eq]
  have h2 : ((m : K)) = algebraMap (𝓞 K) K ((m : 𝓞 K)) := (map_natCast _ m).symm
  rw [h2, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem Q ((m : ℕ) : 𝓞 K) n).mpr h

end ExistsCongruence

open ExistsCongruence

/-! ## The main theorem -/

theorem exists_congruenceSubgroup_le_normImage {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    ∃ m : ℕ, 0 < m ∧ ∃ U : Subgroup (NK.GlobalCFT.Idele K),
      (∀ x : NK.GlobalCFT.Idele K, x ∈ U ↔
        (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
          x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
            NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭)) ∧
        (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal →
          Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((x (NK.GlobalCFT.Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1)
            ≤ Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (((m : ℕ) : 𝔭.adicCompletion K))) ∧
        (∀ w : NumberField.InfinitePlace K,
          NK.CFTLib.Arl.PosAtReal w (x (NK.GlobalCFT.Place.ofInfinite w)))) ∧
      U ≤ NK.GlobalCFT.Idele.normImage K L := by
  classical
  obtain ⟨m, hmpos, hmram⟩ := exists_modulus (K := K) (L := L)
  -- the local norm at the chosen place above each place of `K`
  set Φ : (v : Place K) → (Place.localField L (IdeleHasse.placeAbove v))ˣ →* (Place.localField K v)ˣ :=
    (fun v => match v with
      | Sum.inl w =>
          @Place.localNormInfinite K _ L _ _ (aboveInf (K := K) (L := L) w) w
            (aboveInf_liesOver w)
      | Sum.inr Q =>
          Place.localNormFinite (abovePrime (K := K) (L := L) Q) Q (abovePrime_liesOver Q))
    with hΦdef
  -- the finite set of primes dividing `m`
  have hfin : {Q : HeightOneSpectrum (𝓞 K) | (m : 𝓞 K) ∈ Q.asIdeal}.Finite := by
    refine (Ideal.finite_factors (R := 𝓞 K) (I := Ideal.span {((m : ℕ) : 𝓞 K)}) ?_).subset ?_
    · exact fun h0 => Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hmpos)
        (Ideal.span_singleton_eq_bot.mp h0)
    · intro Q hQ
      exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem Q.asIdeal).mpr hQ)
  set Sfin : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset with hSfindef
  have hSfinmem : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∈ Sfin ↔ (m : 𝓞 K) ∈ Q.asIdeal :=
    fun Q => Set.Finite.mem_toFinset hfin
  set S : Finset (Place K) :=
    (Finset.univ.image Place.ofInfinite) ∪ (Sfin.image Place.ofFinite) with hSdef
  have hSinf : ∀ w : InfinitePlace K, Place.ofInfinite w ∈ S := by
    intro w
    rw [hSdef]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))
  have hSfinmem' : ∀ Q : HeightOneSpectrum (𝓞 K),
      (m : 𝓞 K) ∈ Q.asIdeal → Place.ofFinite Q ∈ S := by
    intro Q hQ
    rw [hSdef]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨Q, (hSfinmem Q).mpr hQ, rfl⟩)
  have hSofFinite : ∀ Q : HeightOneSpectrum (𝓞 K),
      Place.ofFinite Q ∈ S → (m : 𝓞 K) ∈ Q.asIdeal := by
    intro Q hQ
    rw [hSdef] at hQ
    rcases Finset.mem_union.mp hQ with h | h
    · obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
      exact absurd (hw ▸ Place.isInfinite_ofInfinite w) (Place.not_isInfinite_ofFinite Q)
    · obtain ⟨Q', hQ', hQQ'⟩ := Finset.mem_image.mp h
      have h' : Q' = Q := Place.ofFinite_inj.mp hQQ'
      exact h' ▸ (hSfinmem Q').mp hQ'
  -- the congruence subgroup of modulus `m`
  let U : Subgroup (Idele K) :=
    { carrier := {x : Idele K |
        (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
          x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
            NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭)) ∧
        (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal →
          Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((x (NK.GlobalCFT.Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1)
            ≤ Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (((m : ℕ) : 𝔭.adicCompletion K))) ∧
        (∀ w : NumberField.InfinitePlace K,
          NK.CFTLib.Arl.PosAtReal w (x (NK.GlobalCFT.Place.ofInfinite w)))}
      one_mem' := by
        refine ⟨?_, ?_, ?_⟩
        · intro 𝔭 _
          rw [Idele.one_apply]
          exact Subgroup.one_mem _
        · intro 𝔭 _
          rw [Idele.one_apply]
          exact Arl.congrAt_one 𝔭 m
        · intro w
          rw [Idele.one_apply]
          exact Arl.posAtReal_one w
      mul_mem' := by
        intro x y hx hy
        refine ⟨?_, ?_, ?_⟩
        · intro 𝔭 h𝔭
          rw [Idele.mul_apply]
          exact Subgroup.mul_mem _ (hx.1 𝔭 h𝔭) (hy.1 𝔭 h𝔭)
        · intro 𝔭 h𝔭
          rw [Idele.mul_apply]
          exact Arl.congrAt_mul 𝔭 m h𝔭 (hx.2.1 𝔭 h𝔭) (hy.2.1 𝔭 h𝔭)
        · intro w
          rw [Idele.mul_apply]
          exact Arl.posAtReal_mul (hx.2.2 w) (hy.2.2 w)
      inv_mem' := by
        intro x hx
        refine ⟨?_, ?_, ?_⟩
        · intro 𝔭 h𝔭
          rw [Idele.inv_apply]
          exact Subgroup.inv_mem _ (hx.1 𝔭 h𝔭)
        · intro 𝔭 h𝔭
          rw [Idele.inv_apply]
          exact Arl.congrAt_inv 𝔭 m h𝔭 (hx.2.1 𝔭 h𝔭)
        · intro w
          rw [Idele.inv_apply]
          exact Arl.posAtReal_inv (hx.2.2 w) }
  refine ⟨m, hmpos, U, fun x => Iff.rfl, ?_⟩
  -- the identification of `Φ` with the local norms
  have hΦfin : ∀ Q : HeightOneSpectrum (𝓞 K),
      Φ (Place.ofFinite Q) = Place.localNormFinite (abovePrime (K := K) (L := L) Q) Q
        (abovePrime_liesOver Q) := fun Q => rfl
  have hΦinf : ∀ w : InfinitePlace K,
      Φ (Place.ofInfinite w) = @Place.localNormInfinite K _ L _ _
        (aboveInf (K := K) (L := L) w) w (aboveInf_liesOver w) := fun w => rfl
  have hbridge : ∀ (v : Place K) (u : (Place.localField L (IdeleHasse.placeAbove v))ˣ),
      Idele.normIdeleFun K L
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (IdeleHasse.placeAbove v) u)
        v = Φ v u := by
    intro v u
    cases v with
    | inl w =>
        exact NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite
          (v := w) (w := aboveInf (K := K) (L := L) w) (hw := aboveInf_liesOver w) u
    | inr Q =>
        exact NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite
          Q (abovePrime Q) (abovePrime_liesOver Q) u
  -- the congruence subgroup lies in the constrained idèles
  have hU : U ≤ NK.GlobalCFTdeep.constrainedE S (fun v : ↥S => (Φ ↑v).range) := by
    intro x hx
    rw [NK.GlobalCFTdeep.mem_constrainedE]
    refine ⟨fun v => ?_, fun v hvS => ?_⟩
    · rcases hv : (↑v : Place K) with w | Q
      · have hpos : Arl.PosAtReal w (x (Place.ofInfinite w)) := hx.2.2 w
        rw [hΦinf w]
        exact posAtReal_mem_range_localNormInfinite (v := w) (w := aboveInf (K := K) (L := L) w)
          (hw := aboveInf_liesOver w) hpos
      · have hv' : (↑v : Place K) = Place.ofFinite Q := hv
        have hmem : (m : 𝓞 K) ∈ Q.asIdeal := hSofFinite Q (hv' ▸ v.2)
        by_cases hram : Q ∈ ramPrimes (K := K) (L := L)
        · have hpow : (m : 𝓞 K) ∈ Q.asIdeal ^ levelOf (K := K) (L := L) Q := hmram Q hram
          have hvalm : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (((m : ℕ) : Q.adicCompletion K)) ≤
              (WithZero.exp (-((levelOf (K := K) (L := L) Q : ℕ) : ℤ)) :
                WithZero (Multiplicative ℤ)) :=
            val_natCast_le_exp_neg_of_mem_pow Q m (levelOf (K := K) (L := L) Q) hpow
          have hz : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (((x (Place.ofFinite Q) : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) - 1) ≤
              (WithZero.exp (-((levelOf (K := K) (L := L) Q : ℕ) : ℤ)) :
                WithZero (Multiplicative ℤ)) :=
            le_trans (hx.2.1 Q hmem) hvalm
          have hmemr := mem_range_localNormFinite_of_val_le_levelOf Q (x (Place.ofFinite Q)) hz
          rwa [hΦfin Q]
        · have hunr : (abovePrime (K := K) (L := L) Q).asIdeal.ramificationIdx (𝓞 K) = 1 :=
            ramificationIdx_eq_one_of_notMem_ramPrimes hram (abovePrime_liesOver Q)
          have hmemr := mem_range_localNormFinite_of_congr Q (abovePrime Q)
            (abovePrime_liesOver Q) hunr hmem (hx.2.1 Q hmem)
          rwa [hΦfin Q]
    · cases v with
      | inl w => exact absurd (hSinf w) hvS
      | inr Q => exact hx.1 Q (fun hmem => hvS (hSfinmem' Q hmem))
  -- outside `S` the local norm is surjective on the local units
  have hunit : ∀ v : Place K, v ∉ S → ∀ a ∈ Place.localUnits K v,
      ∃ u ∈ Place.localUnits L (IdeleHasse.placeAbove v), Φ v u = a := by
    intro v
    cases v with
    | inl w => exact fun hvS => absurd (hSinf w) hvS
    | inr Q =>
      intro hvS a ha
      have hnotm : (m : 𝓞 K) ∉ Q.asIdeal := fun hmem => hvS (hSfinmem' Q hmem)
      have hnotram : Q ∉ ramPrimes (K := K) (L := L) := fun hram =>
        hnotm (Ideal.pow_le_self (n := levelOf (K := K) (L := L) Q)
          (levelOf_pos Q).ne' (hmram Q hram))
      have hunr : (abovePrime (K := K) (L := L) Q).asIdeal.ramificationIdx (𝓞 K) = 1 :=
        ramificationIdx_eq_one_of_notMem_ramPrimes hnotram (abovePrime_liesOver Q)
      obtain ⟨u, hu, hua⟩ :=
        NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
          Q (abovePrime Q) (abovePrime_liesOver Q) hunr a ha
      refine ⟨u, ?_, ?_⟩
      · show u ∈ Place.localUnits L (Place.ofFinite (abovePrime (K := K) (L := L) Q))
        exact hu
      · show (Place.localNormFinite (abovePrime (K := K) (L := L) Q) Q
          (abovePrime_liesOver Q)) u = a
        exact hua
  exact hU.trans (NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage S (fun v : ↥S => (Φ ↑v).range)
    IdeleHasse.placeAbove IdeleHasse.liesOver_placeAbove Φ hbridge (fun v => le_rfl) hunit)

end

end NK.CFTLib

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
import Submission.Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
import Submission.Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
import Submission.NK.GlobalCFT.Place

set_option linter.unusedSectionVars false

open scoped NumberField
open scoped WithZero WithZeroTopology

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT

section Finite
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem globalCFT_valuation_smulHeightOneSpectrum (σ : L ≃ₐ[K] L)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (x : L) :
    (Place.smulHeightOneSpectrum σ q).valuation L (σ.toRingEquiv x) = q.valuation L x :=
  Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq (R := 𝓞 L) (K := L)
    (Place.ringOfIntegersEquiv σ) σ.toRingEquiv (fun _ => rfl) q
    (Place.smulHeightOneSpectrum σ q) (Place.smulHeightOneSpectrum_asIdeal σ q) x

theorem globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum (σ : L ≃ₐ[K] L)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    UniformContinuous (WithVal.congr (q.valuation L)
      ((Place.smulHeightOneSpectrum σ q).valuation L) σ.toRingEquiv) :=
  Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
    (WithVal.congr (q.valuation L) ((Place.smulHeightOneSpectrum σ q).valuation L)
      σ.toRingEquiv).toRingHom
    (by
      intro x
      change (WithVal.valuation ((Place.smulHeightOneSpectrum σ q).valuation L))
          ((WithVal.congr (q.valuation L) ((Place.smulHeightOneSpectrum σ q).valuation L)
            σ.toRingEquiv) x) = (WithVal.valuation (q.valuation L)) x
      rw [WithVal.congr_apply, WithVal.valuation_apply_eq_ofVal, WithVal.ofVal_toVal,
        WithVal.valuation_apply_eq_ofVal]
      exact globalCFT_valuation_smulHeightOneSpectrum σ q x.ofVal)
    (by
      intro γ hγ
      obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective L q γ
      exact ⟨WithVal.toVal (q.valuation L) y, by rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ,
        by rw [WithVal.valuation_apply_eq_ofVal, hy]⟩)

theorem globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum_symm (σ : L ≃ₐ[K] L)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    UniformContinuous (WithVal.congr (q.valuation L)
      ((Place.smulHeightOneSpectrum σ q).valuation L) σ.toRingEquiv).symm := by
  rw [WithVal.congr_symm]
  exact Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
    (WithVal.congr ((Place.smulHeightOneSpectrum σ q).valuation L) (q.valuation L)
      σ.toRingEquiv.symm).toRingHom
    (by
      intro x
      change (WithVal.valuation (q.valuation L))
          ((WithVal.congr ((Place.smulHeightOneSpectrum σ q).valuation L) (q.valuation L)
            σ.toRingEquiv.symm) x) =
          (WithVal.valuation ((Place.smulHeightOneSpectrum σ q).valuation L)) x
      rw [WithVal.congr_apply, WithVal.valuation_apply_eq_ofVal, WithVal.ofVal_toVal,
        WithVal.valuation_apply_eq_ofVal]
      have h := globalCFT_valuation_smulHeightOneSpectrum σ q ((σ.toRingEquiv).symm x.ofVal)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm)
    (by
      intro γ hγ
      obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective L
        (Place.smulHeightOneSpectrum σ q) γ
      exact ⟨WithVal.toVal ((Place.smulHeightOneSpectrum σ q).valuation L) y,
        by rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ,
        by rw [WithVal.valuation_apply_eq_ofVal, hy]⟩)

/-- The `WithVal`-level ring isomorphism of completions induced by `σ`. -/
noncomputable def globalCFT_withValCongrEquiv (σ : L ≃ₐ[K] L)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    UniformSpace.Completion (WithVal (q.valuation L)) ≃+*
      UniformSpace.Completion (WithVal ((Place.smulHeightOneSpectrum σ q).valuation L)) :=
  UniformSpace.Completion.mapRingEquiv
    (WithVal.congr (q.valuation L) ((Place.smulHeightOneSpectrum σ q).valuation L) σ.toRingEquiv)
    (globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum σ q).continuous
    (globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum_symm σ q).continuous

variable (σ : L ≃ₐ[K] L) (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))

theorem globalCFT_withValCongrEquiv_coe (y : WithVal (q.valuation L)) :
    globalCFT_withValCongrEquiv σ q
        (y : UniformSpace.Completion (WithVal (q.valuation L)))
      = ((WithVal.congr (q.valuation L) ((Place.smulHeightOneSpectrum σ q).valuation L)
          σ.toRingEquiv) y :
        UniformSpace.Completion (WithVal ((Place.smulHeightOneSpectrum σ q).valuation L))) := by
  rw [globalCFT_withValCongrEquiv, UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe]
  exact globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum σ q

theorem globalCFT_algebraMap_valuationCompletion (x : L) :
    algebraMap L ((q.valuation L).Completion) x
      = (WithVal.toVal (q.valuation L) x :
        UniformSpace.Completion (WithVal (q.valuation L))) := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply]
  simp

theorem globalCFT_algebraMap_eq_coe (y : L) :
    algebraMap L (q.adicCompletion L) y = (y : q.adicCompletion L) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp

/-- The ring isomorphism of adic completions induced by a `K`-algebra automorphism `σ`. -/
noncomputable def globalCFT_adicCongrEquiv :
    q.adicCompletion L ≃+* (Place.smulHeightOneSpectrum σ q).adicCompletion L :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L q).trans
    ((globalCFT_withValCongrEquiv σ q).trans
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L
        (Place.smulHeightOneSpectrum σ q)).symm)

theorem globalCFT_adicCongrEquiv_algebraMap (x : L) :
    globalCFT_adicCongrEquiv σ q (algebraMap L (q.adicCompletion L) x) =
      algebraMap L ((Place.smulHeightOneSpectrum σ q).adicCompletion L) (σ.toRingEquiv x) := by
  rw [globalCFT_adicCongrEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply]
  have h1 : (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L q)
      (algebraMap L (q.adicCompletion L) x) = algebraMap L ((q.valuation L).Completion) x := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv_apply]
    exact IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion_toCompletion
      (R := 𝓞 L) (K := L) (S := L) q x
  rw [h1]
  rw [globalCFT_algebraMap_valuationCompletion (q := q) x, globalCFT_withValCongrEquiv_coe σ q,
    WithVal.congr_apply, WithVal.ofVal_toVal]
  rw [← globalCFT_algebraMap_valuationCompletion (q := Place.smulHeightOneSpectrum σ q) (σ.toRingEquiv x)]
  rw [← IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion_toCompletion
    (R := 𝓞 L) (K := L) (S := L) (Place.smulHeightOneSpectrum σ q) (σ.toRingEquiv x)]
  rfl

theorem globalCFT_withValCongrEquiv_continuous :
    Continuous (globalCFT_withValCongrEquiv σ q) := by
  have h : ⇑(globalCFT_withValCongrEquiv σ q) =
      UniformSpace.Completion.map ⇑(WithVal.congr (q.valuation L)
        ((Place.smulHeightOneSpectrum σ q).valuation L) σ.toRingEquiv) := by
    funext a
    rw [globalCFT_withValCongrEquiv, UniformSpace.Completion.mapRingEquiv_apply]
  rw [h]
  exact UniformSpace.Completion.continuous_map

theorem globalCFT_adicCongrEquiv_continuous :
    Continuous (globalCFT_adicCongrEquiv σ q) := by
  have h : ⇑(globalCFT_adicCongrEquiv σ q) =
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion (R := 𝓞 L) (K := L)
          (v := Place.smulHeightOneSpectrum σ q)) ∘
        (⇑(globalCFT_withValCongrEquiv σ q) ∘
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion (R := 𝓞 L) (K := L)
            (v := q))) := by
    funext a
    simp only [Function.comp_apply, globalCFT_adicCongrEquiv, RingEquiv.trans_apply,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv_apply]
    rfl
  rw [h]
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion L
    (Place.smulHeightOneSpectrum σ q)).comp
    ((globalCFT_withValCongrEquiv_continuous σ q).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion L q))

theorem globalCFT_adicCongrEquiv_coe (x : L) :
    globalCFT_adicCongrEquiv σ q (x : q.adicCompletion L) =
      ((σ.toRingEquiv x : L) : (Place.smulHeightOneSpectrum σ q).adicCompletion L) := by
  rw [← globalCFT_algebraMap_eq_coe (q := q) x, globalCFT_adicCongrEquiv_algebraMap σ q x,
    globalCFT_algebraMap_eq_coe (q := Place.smulHeightOneSpectrum σ q) (σ.toRingEquiv x)]

theorem globalCFT_adicCongrEquiv_valued (y : q.adicCompletion L) :
    Valued.v (globalCFT_adicCongrEquiv σ q y) = Valued.v y := by
  have hdense : DenseRange ((↑) : L → q.adicCompletion L) := by
    have h := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) L q
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] at h
    simpa using h
  have hcont1 : Continuous (fun y : q.adicCompletion L => Valued.v (globalCFT_adicCongrEquiv σ q y)) :=
    (Valued.continuous_valuation_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective L
        (Place.smulHeightOneSpectrum σ q))).comp (globalCFT_adicCongrEquiv_continuous σ q)
  have hcont2 : Continuous (fun y : q.adicCompletion L => Valued.v y) :=
    Valued.continuous_valuation_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective L q)
  have heq : (fun y : q.adicCompletion L => Valued.v (globalCFT_adicCongrEquiv σ q y)) =
      fun y => Valued.v y :=
    hdense.equalizer hcont1 hcont2 (by
      funext x
      rw [Function.comp_apply, Function.comp_apply, globalCFT_adicCongrEquiv_coe σ q x,
        IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe,
        IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
      simpa using globalCFT_valuation_smulHeightOneSpectrum σ q x)
  exact congrFun heq y

theorem globalCFT_adicCongrEquiv_localUnits (u : (q.adicCompletion L)ˣ) :
    u ∈ Place.localUnits L (Place.ofFinite q) ↔
      Units.map (globalCFT_adicCongrEquiv σ q).toMonoidHom u ∈
        Place.localUnits L (Place.ofFinite (Place.smulHeightOneSpectrum σ q)) := by
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one,
    Place.mem_localUnits_ofFinite_iff_valued_eq_one, Units.coe_map]
  change Valued.v ((u : (q.adicCompletion L)ˣ) : q.adicCompletion L) = 1 ↔
    Valued.v ((globalCFT_adicCongrEquiv σ q) ↑u) = 1
  rw [globalCFT_adicCongrEquiv_valued σ q (u : q.adicCompletion L)]

/-- The nonarchimedean case of the functoriality of the local field. -/
theorem globalCFT_exists_localRingEquiv_smul_finite :
    ∃ e : q.adicCompletion L ≃+* (Place.smulHeightOneSpectrum σ q).adicCompletion L,
      (∀ x : L, e (algebraMap L (q.adicCompletion L) x) =
        algebraMap L ((Place.smulHeightOneSpectrum σ q).adicCompletion L) (σ x)) ∧
      (∀ u : (q.adicCompletion L)ˣ,
        u ∈ Place.localUnits L (Place.ofFinite q) ↔
          Units.map e.toMonoidHom u ∈ Place.localUnits L
            (Place.ofFinite (Place.smulHeightOneSpectrum σ q))) :=
  ⟨globalCFT_adicCongrEquiv σ q,
    fun x => globalCFT_adicCongrEquiv_algebraMap σ q x,
    fun u => globalCFT_adicCongrEquiv_localUnits σ q u⟩

end Finite

section Infinite
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The ring equivalence `WithAbs w.1 ≃+* WithAbs ((σ • w).1)` induced by `σ`. -/
noncomputable def globalCFT_withAbsCongrEquiv (σ : L ≃ₐ[K] L) (w : NumberField.InfinitePlace L) :
    WithAbs w.1 ≃+* WithAbs ((σ • w).1) :=
  WithAbs.congr w.1 ((σ • w).1) σ.toRingEquiv

theorem globalCFT_withAbsCongrEquiv_norm (σ : L ≃ₐ[K] L) (w : NumberField.InfinitePlace L)
    (z : WithAbs w.1) : ‖globalCFT_withAbsCongrEquiv σ w z‖ = ‖z‖ := by
  rw [globalCFT_withAbsCongrEquiv, WithAbs.congr_apply, WithAbs.norm_toAbs_eq,
    WithAbs.norm_eq_apply_ofAbs]
  rw [← NumberField.InfinitePlace.coe_apply, ← NumberField.InfinitePlace.coe_apply,
    NumberField.InfinitePlace.smul_apply]
  congr 1
  simp

theorem globalCFT_isometry_withAbsCongrEquiv (σ : L ≃ₐ[K] L) (w : NumberField.InfinitePlace L) :
    Isometry (globalCFT_withAbsCongrEquiv σ w) := by
  rw [isometry_iff_dist_eq]
  intro x y
  simp only [dist_eq_norm, ← map_sub]
  rw [globalCFT_withAbsCongrEquiv_norm]

theorem globalCFT_isometry_withAbsCongrEquiv_symm (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) :
    Isometry (globalCFT_withAbsCongrEquiv σ w).symm := by
  have hnorm : ∀ z : WithAbs ((σ • w).1),
      ‖(WithAbs.congr ((σ • w).1) (w.1) σ.toRingEquiv.symm) z‖ = ‖z‖ := by
    intro z
    rw [WithAbs.congr_apply, WithAbs.norm_toAbs_eq, WithAbs.norm_eq_apply_ofAbs]
    rw [← NumberField.InfinitePlace.coe_apply, ← NumberField.InfinitePlace.coe_apply,
      NumberField.InfinitePlace.smul_apply]
    simp
  rw [globalCFT_withAbsCongrEquiv, WithAbs.congr_symm]
  rw [isometry_iff_dist_eq]
  intro x y
  simp only [dist_eq_norm, ← map_sub]
  rw [hnorm]

/-- The ring isomorphism of archimedean completions induced by `σ`. -/
noncomputable def globalCFT_infiniteCongrEquiv (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) : w.Completion ≃+* (σ • w).Completion :=
  (NumberField.InfinitePlace.Completion.equiv w).trans
    ((UniformSpace.Completion.mapRingEquiv (globalCFT_withAbsCongrEquiv σ w)
        (globalCFT_isometry_withAbsCongrEquiv σ w).continuous
        (globalCFT_isometry_withAbsCongrEquiv_symm σ w).continuous).trans
      (NumberField.InfinitePlace.Completion.equiv (σ • w)).symm)

theorem globalCFT_infiniteCongrEquiv_algebraMap (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) (x : L) :
    globalCFT_infiniteCongrEquiv σ w (algebraMap L w.Completion x) =
      algebraMap L (σ • w).Completion (σ x) := by
  have h1 : (NumberField.InfinitePlace.Completion.equiv w) (algebraMap L w.Completion x)
      = algebraMap L (w.1.Completion) x := by
    rw [NumberField.InfinitePlace.Completion.equiv_apply]
    exact NumberField.InfinitePlace.Completion.algebraMap_toCompletion w L x
  have h2 : (UniformSpace.Completion.mapRingEquiv (globalCFT_withAbsCongrEquiv σ w)
        (globalCFT_isometry_withAbsCongrEquiv σ w).continuous
        (globalCFT_isometry_withAbsCongrEquiv_symm σ w).continuous)
        (algebraMap L (w.1.Completion) x)
      = algebraMap L ((σ • w).1.Completion) (σ x) := by
    have hcoe : algebraMap L (w.1.Completion) x
        = (WithAbs.toAbs w.1 x : UniformSpace.Completion (WithAbs w.1)) := by
      rw [UniformSpace.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
      simp
    rw [hcoe, UniformSpace.Completion.mapRingEquiv_apply, UniformSpace.Completion.map_coe]
    · rw [globalCFT_withAbsCongrEquiv, WithAbs.congr_apply]
      rw [UniformSpace.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
      simp
    · exact uniformContinuous_addMonoidHom_of_continuous
        (globalCFT_isometry_withAbsCongrEquiv σ w).continuous
  have h3 : (NumberField.InfinitePlace.Completion.equiv (σ • w)).symm
      (algebraMap L ((σ • w).1.Completion) (σ x))
      = algebraMap L ((σ • w).Completion) (σ x) := by
    rw [← NumberField.InfinitePlace.Completion.algebraMap_toCompletion (σ • w) L (σ x)]
    rfl
  rw [globalCFT_infiniteCongrEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, h1, h2, h3]

/-- The archimedean case of the functoriality of the local field. -/
theorem globalCFT_exists_localRingEquiv_smul_infinite (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) :
    ∃ e : w.Completion ≃+* (σ • w).Completion,
      (∀ x : L, e (algebraMap L w.Completion x) = algebraMap L (σ • w).Completion (σ x)) ∧
      (∀ u : (w.Completion)ˣ,
        u ∈ Place.localUnits L (Place.ofInfinite w) ↔
          Units.map e.toMonoidHom u ∈ Place.localUnits L (Place.ofInfinite (σ • w))) :=
  ⟨globalCFT_infiniteCongrEquiv σ w,
    fun x => globalCFT_infiniteCongrEquiv_algebraMap σ w x,
    fun u => by simp [Place.localUnits_ofInfinite]⟩

end Infinite

theorem globalCFT_exists_localRingEquiv_smul {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (v : NK.GlobalCFT.Place L) :
    ∃ e : (NK.GlobalCFT.Place.localField L v) ≃+* (NK.GlobalCFT.Place.localField L (σ • v)),
      (∀ x : L, e (algebraMap L (NK.GlobalCFT.Place.localField L v) x) =
        algebraMap L (NK.GlobalCFT.Place.localField L (σ • v)) (σ x)) ∧
      (∀ u : (NK.GlobalCFT.Place.localField L v)ˣ,
        u ∈ NK.GlobalCFT.Place.localUnits L v ↔
          Units.map e.toMonoidHom u ∈ NK.GlobalCFT.Place.localUnits L (σ • v)) := by
  cases v with
  | inl w =>
      obtain ⟨e, h1, h2⟩ := globalCFT_exists_localRingEquiv_smul_infinite σ w
      exact ⟨e, h1, h2⟩
  | inr q =>
      obtain ⟨e, h1, h2⟩ := globalCFT_exists_localRingEquiv_smul_finite σ q
      exact ⟨e, h1, h2⟩

end NK.GlobalCFT.Galois

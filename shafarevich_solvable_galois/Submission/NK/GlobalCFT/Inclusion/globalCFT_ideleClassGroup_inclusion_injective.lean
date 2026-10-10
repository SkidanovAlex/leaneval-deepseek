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
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.NK.FieldTheory.Galois.iSup_decompositionSubgroup_eq_top
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.GlobalCFT.Norm.NormTransAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Injectivity of the inclusion of idèle class groups

For a finite extension `L / K` of number fields and a monoid homomorphism `phi : 𝕀 K →* 𝕀 L`
whose `w`-component is the local embedding `K_{u w}ˣ →* L_wˣ`, the induced map on idèle class
groups `C_K →* C_L` is **injective**.

The mathematical content is the standard fact that the inclusion `C_K → C_L` has trivial
kernel: if an idèle `x` of `K` becomes principal in `L`, then it is already principal in `K`.
Writing `phi x = (y)` for `y ∈ Lˣ`, this reduces to the "local global" statement

  `y ∈ Lˣ` lies in the image of every local field `K_v` inside `L_w` (for all places `v`, `w | v`)
  only if `y ∈ Kˣ`,

which is proved as `globalCFT_mem_base_of_localUnits` below via Čebotarev's theorem in the form of
`NK.FieldTheory.Galois.iSup_decompositionSubgroup_eq_top` ("the decomposition subgroups of a
finite Galois extension of number fields generate the Galois group"): passing to the normal
closure `N` of `L / K`, every decomposition subgroup `D_w ⊆ Gal(N/K)` fixes the image of `y` in
`N` (because `y ∈ K_v` inside `N_w` and `D_w ≅ Gal(N_w/K_v)` acts by `K_v`-algebra
automorphisms), hence so does all of `Gal(N/K)`, and `y ∈ K` follows from the Galois
correspondence.

## Main result

* `NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Inclusion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The local algebra map `K_vˣ →* L_wˣ` does not depend on the proof of `LiesOver`. -/
theorem globalCFT_localAlgebraMapUnits_congr (w : Place L) (v : Place K)
    (h h' : Place.LiesOver w v) :
    Place.localAlgebraMapUnits w v h = Place.localAlgebraMapUnits w v h' := rfl

/-- At an archimedean place the local algebra map on unit groups is `Units.map` of the
canonical ring homomorphism `K_v →+* L_w` of completions. -/
theorem globalCFT_localAlgebraMapUnits_ofInfinite (w : InfinitePlace L) (v : InfinitePlace K)
    [hwv : w.LiesOver v] (h : Place.LiesOver (Place.ofInfinite w) (Place.ofInfinite v)) :
    Place.localAlgebraMapUnits (Place.ofInfinite w) (Place.ofInfinite v) h =
      Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom := by
  rw [globalCFT_localAlgebraMapUnits_congr (Place.ofInfinite w) (Place.ofInfinite v) h
    (Place.liesOver_ofInfinite hwv)]
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hwv]

/-- At a nonarchimedean place the local algebra map on unit groups is `Units.map` of the adic
completion map `K_Q →+* L_q`. -/
theorem globalCFT_localAlgebraMapUnits_ofFinite (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) [hqQ : q.asIdeal.LiesOver Q.asIdeal]
    (h : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q)) :
    Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) h =
      Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom := by
  rw [globalCFT_localAlgebraMapUnits_congr (Place.ofFinite q) (Place.ofFinite Q) h
    (Place.liesOver_ofFinite hqQ)]
  unfold Place.localAlgebraMapUnits
  simp only [dif_pos hqQ]

/-- **The local algebra map is injective.**  If `w` lies over `v` then the two places are of
the same kind (both archimedean or both nonarchimedean) and the local map is `Units.map` of an
injective ring homomorphism of fields, hence injective. -/
theorem globalCFT_localAlgebraMapUnits_injective {w : Place L} {v : Place K}
    (h : Place.LiesOver w v) :
    Function.Injective (Place.localAlgebraMapUnits w v h) := by
  rcases (Place.liesOver_iff w v).mp h with ⟨w', v', hw, hv, hL⟩ | ⟨q, Q, hw, hv, hL⟩
  · subst hw; subst hv
    haveI := hL
    rw [globalCFT_localAlgebraMapUnits_ofInfinite (w := w') (v := v') h]
    exact Units.map_injective (RingHom.injective _)
  · subst hw; subst hv
    haveI := hL
    rw [globalCFT_localAlgebraMapUnits_ofFinite (q := q) (Q := Q) h]
    exact Units.map_injective (RingHom.injective _)

end NK.GlobalCFT.Inclusion

namespace NK.GlobalCFT.Inclusion

variable {K N : Type*} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

/-- **The decomposition group fixes the embedded copy of `K_p`.**  If `y : N` has its image in
`N_w` inside the image of `K_p`, then every element of the decomposition subgroup of `w` fixes
`y`: the decomposition group acts on `N_w` by `K_p`-algebra automorphisms. -/
theorem globalCFT_fixed_of_mem_range_adicCompletionMap
    (p : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 N))
    (hw : w.asIdeal.LiesOver p.asIdeal)
    (y : N) (hy : algebraMap N (w.adicCompletion N) y ∈
      Set.range (Commons.RingTheory.Henselian.adicCompletionMap p w hw))
    (σ : NK.FieldTheory.Galois.decompSubgroup (K := K) w) : σ.1 y = y := by
  obtain ⟨t, ht⟩ := hy
  have ht0 : Commons.RingTheory.Henselian.adicCompletionMap p w hw t =
      (y : w.adicCompletion N) := by
    simpa [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] using ht
  have h1 : Submission.NeukirchUchida.Local.decompositionToAdicCompletion (K := K) w σ
      (y : w.adicCompletion N) = (σ.1 y : w.adicCompletion N) :=
    Submission.NeukirchUchida.Local.decompositionToAdicCompletion_coe (K := K) w σ y
  have h2 : Submission.NeukirchUchida.Local.decompositionToAdicCompletion (K := K) w σ
      (Commons.RingTheory.Henselian.adicCompletionMap p w hw t) =
      Commons.RingTheory.Henselian.adicCompletionMap p w hw t :=
    Submission.NeukirchUchida.Local.decompositionToAdicCompletion_adicCompletionMap p w hw σ t
  have h3 : (σ.1 y : w.adicCompletion N) = (y : w.adicCompletion N) := by
    rw [← h1, ← ht0, h2]
  simpa using Submission.NeukirchUchida.Local.injective_algebraMap_adicCompletion w h3

end NK.GlobalCFT.Inclusion

namespace NK.GlobalCFT.Inclusion

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

/-- The adic completion map is compatible with the algebra maps along a tower
`K → L → M`. -/
theorem globalCFT_adicCompletionMap_algebraMap
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : K) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq
        (algebraMap K (Q.adicCompletion K) x) =
      algebraMap L (q.adicCompletion L) (algebraMap K L x) := by
  have h1 : algebraMap K (Q.adicCompletion K) x = (x : Q.adicCompletion K) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  have h2 : (algebraMap K L x : q.adicCompletion L) =
      algebraMap L (q.adicCompletion L) (algebraMap K L x) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  rw [h1, ← h2, Commons.RingTheory.Henselian.adicCompletionMap_apply]

/-- **The local condition transfers along a tower.**  If the image of `y ∈ Lˣ` in `L_q` lies in
the image of `K_p`, then the image of `y` in `M_r` lies in the image of `K_p`, for every prime
`r` of `M` over `q`. -/
theorem globalCFT_mem_range_adicCompletionMap_comp
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) (r : HeightOneSpectrum (𝓞 M))
    (hpq : q.asIdeal.LiesOver p.asIdeal) (hqr : r.asIdeal.LiesOver q.asIdeal)
    (hpr : r.asIdeal.LiesOver p.asIdeal)
    (y : Lˣ)
    (hy : Units.map (algebraMap L (q.adicCompletion L)) y ∈
      Set.range (Units.map
        (Commons.RingTheory.Henselian.adicCompletionMap p q hpq).toMonoidHom)) :
    Units.map (algebraMap M (r.adicCompletion M)) (Units.map (algebraMap L M).toMonoidHom y) ∈
      Set.range (Units.map
        (Commons.RingTheory.Henselian.adicCompletionMap p r hpr).toMonoidHom) := by
  obtain ⟨t, ht⟩ := hy
  refine ⟨t, ?_⟩
  have ht' : Commons.RingTheory.Henselian.adicCompletionMap p q hpq (t : p.adicCompletion K) =
      algebraMap L (q.adicCompletion L) (y : L) := by
    have h := congrArg (fun u : (q.adicCompletion L)ˣ => (u : q.adicCompletion L)) ht
    simpa using h
  apply Units.ext
  simp only [Units.coe_map]
  calc Commons.RingTheory.Henselian.adicCompletionMap p r hpr (t : p.adicCompletion K)
      = (Commons.RingTheory.Henselian.adicCompletionMap q r hqr).comp
          (Commons.RingTheory.Henselian.adicCompletionMap p q hpq)
            (t : p.adicCompletion K) := by
        rw [Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp
          (K := K) (L := L) (M := M) p q r hpq hqr hpr]
    _ = Commons.RingTheory.Henselian.adicCompletionMap q r hqr
          (Commons.RingTheory.Henselian.adicCompletionMap p q hpq (t : p.adicCompletion K)) := rfl
    _ = Commons.RingTheory.Henselian.adicCompletionMap q r hqr
          (algebraMap L (q.adicCompletion L) (y : L)) := by rw [ht']
    _ = algebraMap M (r.adicCompletion M) (algebraMap L M (y : L)) :=
        globalCFT_adicCompletionMap_algebraMap q r hqr (y : L)

end NK.GlobalCFT.Inclusion

namespace NK.GlobalCFT.Inclusion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **A global unit which is locally in the base field is in the base field.**  If `y ∈ Lˣ` has
its image in `L_w` inside the embedded copy of `K_v` for every place `w` of `L` over every place
`v` of `K`, then `y` is the image of a unit of `K`.

We pass to the normal closure `N` of `L/K`.  Every decomposition subgroup `D_w ≤ Gal(N/K)` fixes
the image `y'` of `y` in `N`, because `y' ∈ K_p` inside `N_w` and `D_w` acts on `N_w` by
`K_p`-algebra automorphisms (`globalCFT_fixed_of_mem_range_adicCompletionMap`).  Since the
decomposition subgroups generate `Gal(N/K)` (`NK.FieldTheory.Galois.iSup_decompositionSubgroup_eq_top`),
all of `Gal(N/K)` fixes `y'`, so `y'` lies in the base field by
`IsGalois.mem_range_algebraMap_iff_fixed`. -/
theorem globalCFT_mem_base_of_localUnits
    (y : Lˣ)
    (h : ∀ (v : Place K) (w : Place L) (hwv : Place.LiesOver w v),
      ∃ t : (Place.localField K v)ˣ,
        Place.localAlgebraMapUnits w v hwv t =
          Units.map (algebraMap L (Place.localField L w)) y) :
    ∃ a : Kˣ, Units.map (algebraMap K L).toMonoidHom a = y := by
  classical
  let Ω := AlgebraicClosure L
  let N : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  haveI hAlgL : Algebra.IsAlgebraic L Ω := inferInstance
  haveI hAlgK : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans (R := K) (S := L) (A := Ω)
  haveI hNormK : Normal K Ω :=
    { isAlgebraic := fun x => hAlgK.isAlgebraic x
      splits' := fun x => IsAlgClosed.splits _ }
  haveI hNormN : Normal K ↥N := inferInstance
  haveI hfdN : FiniteDimensional K ↥N := inferInstance
  haveI hNFN : NumberField ↥N :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := Ω) N
  haveI hGalN : IsGalois K ↥N :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero (F := K) (E := ↥N)
  have hyN : algebraMap L Ω (y : L) ∈ N := by
    have hle : (IsScalarTower.toAlgHom K L Ω).fieldRange ≤ N :=
      AlgHom.fieldRange_le_normalClosure _
    have hmem : algebraMap L Ω (y : L) ∈ (IsScalarTower.toAlgHom K L Ω).fieldRange :=
      ⟨(y : L), rfl⟩
    exact hle hmem
  let y' : ↥N := ⟨algebraMap L Ω (y : L), hyN⟩
  have hloc : ∀ (w : HeightOneSpectrum (𝓞 ↥N)) (σ : ↥N ≃ₐ[K] ↥N),
      σ ∈ NK.FieldTheory.Galois.decompSubgroup (K := K) w → σ • y' = y' := by
    intro w σ hσ
    set p : HeightOneSpectrum (𝓞 K) := IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w with hp
    set wL : HeightOneSpectrum (𝓞 L) := IsDedekindDomain.HeightOneSpectrum.under (𝓞 L) w with hwL
    have hwNp : w.asIdeal.LiesOver p.asIdeal := by
      rw [hp, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact Ideal.over_under w.asIdeal
    have hwLw : w.asIdeal.LiesOver wL.asIdeal := by
      rw [hwL, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact Ideal.over_under w.asIdeal
    have hwLp : wL.asIdeal.LiesOver p.asIdeal := by
      rw [hwL, hp, IsDedekindDomain.HeightOneSpectrum.under_asIdeal,
        IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      refine ⟨?_⟩
      rw [Ideal.under_under]
    obtain ⟨t, ht⟩ := h (Place.ofFinite p) (Place.ofFinite wL) (Place.liesOver_ofFinite hwLp)
    have htl : Units.map (algebraMap L (wL.adicCompletion L)) y ∈
        Set.range (Units.map
          (Commons.RingTheory.Henselian.adicCompletionMap p wL hwLp).toMonoidHom) := by
      refine ⟨t, ?_⟩
      have ht' : Place.localAlgebraMapUnits (Place.ofFinite wL) (Place.ofFinite p)
          (Place.liesOver_ofFinite hwLp) t =
          Units.map (algebraMap L (wL.adicCompletion L)) y := ht
      rw [globalCFT_localAlgebraMapUnits_ofFinite (q := wL) (Q := p)
        (h := Place.liesOver_ofFinite hwLp)] at ht'
      exact ht'
    obtain ⟨s, hs⟩ := globalCFT_mem_range_adicCompletionMap_comp p wL w hwLp hwLw hwNp y htl
    have hrange : algebraMap ↥N (w.adicCompletion ↥N) y' ∈ Set.range
        (Commons.RingTheory.Henselian.adicCompletionMap p w hwNp) := by
      obtain ⟨s, hs⟩ := globalCFT_mem_range_adicCompletionMap_comp p wL w hwLp hwLw hwNp y htl
      refine ⟨(s : p.adicCompletion K), ?_⟩
      have hyy : ((Units.map (algebraMap L ↥N) y : (↥N)ˣ) : ↥N) = y' := by
        rw [Units.coe_map]
        rfl
      have h1 : Commons.RingTheory.Henselian.adicCompletionMap p w hwNp
            (s : p.adicCompletion K) =
          algebraMap ↥N (w.adicCompletion ↥N)
            ((Units.map (algebraMap L ↥N) y : (↥N)ˣ) : ↥N) := by
        have h := congrArg (fun u : (w.adicCompletion ↥N)ˣ => (u : w.adicCompletion ↥N)) hs
        simpa using h
      rw [h1, hyy]
    have hfix := globalCFT_fixed_of_mem_range_adicCompletionMap p w hwNp y' hrange ⟨σ, hσ⟩
    simpa using hfix
  have htop := NK.FieldTheory.Galois.iSup_decompositionSubgroup_eq_top (K := K) (L := ↥N)
  have hstab : (⊤ : Subgroup (↥N ≃ₐ[K] ↥N)) ≤ MulAction.stabilizer (↥N ≃ₐ[K] ↥N) y' := by
    rw [← htop]
    apply iSup_le
    intro w σ hσ
    rw [MulAction.mem_stabilizer_iff]
    exact hloc w σ hσ
  have hfix : ∀ σ : ↥N ≃ₐ[K] ↥N, σ y' = y' := by
    intro σ
    have h2 := hstab (Subgroup.mem_top σ)
    rw [MulAction.mem_stabilizer_iff] at h2
    exact h2
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed y').mpr hfix
  have ha0 : a ≠ 0 := by
    intro h0
    have hzero : y' = 0 := by rw [← ha, h0, map_zero]
    have h0' : algebraMap L Ω (y : L) = 0 := by
      have := congrArg (fun z : ↥N => (z : Ω)) hzero
      simpa [y'] using this
    exact (Units.ne_zero y) ((algebraMap L Ω).injective (by simpa using h0'))
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  simp only [Units.coe_map]
  have hay : algebraMap K L a = (y : L) := by
    apply (algebraMap L Ω).injective
    calc algebraMap L Ω (algebraMap K L a)
        = algebraMap K Ω a := (IsScalarTower.algebraMap_apply K L Ω a).symm
      _ = algebraMap ↥N Ω (algebraMap K ↥N a) := (IsScalarTower.algebraMap_apply K ↥N Ω a).symm
      _ = algebraMap ↥N Ω y' := by rw [ha]
      _ = algebraMap L Ω (y : L) := rfl
  exact hay

end NK.GlobalCFT.Inclusion

namespace NK.GlobalCFT.Inclusion

/-- Every place of `K` has a place of `L` above it. -/
theorem exists_place_liesOver {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (v : Place K) :
    ∃ w : Place L, Place.LiesOver w v := by
  rcases v with v' | Q
  · obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v' :=
      InfinitePlace.comap_surjective (k := K) (K := L) v'
    exact ⟨Place.ofInfinite w,
      Place.liesOver_ofInfinite ((NK.GlobalCFT.Norm.liesOver_iff_comap_eq w v').mpr hw)⟩
  · obtain ⟨q, hq⟩ : ∃ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver Q.asIdeal :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver Q
    exact ⟨Place.ofFinite q, Place.liesOver_ofFinite hq⟩

theorem globalCFT_principalIdele_localAlgebraMapUnits {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (a : Kˣ) (w : Place L) :
    Place.localAlgebraMapUnits w (u w) (hu w) ((Idele.principalIdele K a) (u w)) =
      Units.map (algebraMap L (Place.localField L w))
        (Units.map (algebraMap K L).toMonoidHom a) := by
  have h := congrArg (fun z : 𝕀[L] => z w)
    (globalCFT_ideleInclusion_principalIdele u hu φ hφ a)
  simpa [hφ (Idele.principalIdele K a) w, Idele.principalIdele_apply] using h

theorem globalCFT_ideleClassGroup_inclusion_injective {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (ψ : C[K] →* C[L])
    (hψ : ∀ x : 𝕀[K], ψ (IdeleClassGroup.mk K x) = IdeleClassGroup.mk L (φ x)) :
    Function.Injective ψ := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro q hq
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K q
  rw [MonoidHom.mem_ker, hψ x] at hq
  have hmem : φ x ∈ Idele.principalSubgroup L := (QuotientGroup.eq_one_iff (φ x)).mp hq
  obtain ⟨y, hy⟩ := Idele.mem_principalSubgroup.mp hmem
  have hloc : ∀ (v : Place K) (w : Place L) (hwv : Place.LiesOver w v),
      ∃ t : (Place.localField K v)ˣ,
        Place.localAlgebraMapUnits w v hwv t =
          Units.map (algebraMap L (Place.localField L w)) y := by
    intro v w hwv
    have huw : u w = v := globalCFT_liesOver_unique (hu w) hwv
    subst huw
    refine ⟨x (u w), ?_⟩
    have h1 : Place.localAlgebraMapUnits w (u w) hwv (x (u w)) =
        Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)) :=
      DFunLike.congr_fun (globalCFT_localAlgebraMapUnits_congr w (u w) hwv (hu w)) (x (u w))
    rw [h1, ← hφ x w, ← hy]
    exact Idele.principalIdele_apply y w
  obtain ⟨a, ha⟩ := globalCFT_mem_base_of_localUnits y hloc
  have hx : x = Idele.principalIdele K a := by
    apply Idele.ext
    intro v
    obtain ⟨w, hwv⟩ : ∃ w : Place L, Place.LiesOver w v := exists_place_liesOver v
    have huw : u w = v := globalCFT_liesOver_unique (hu w) hwv
    subst huw
    apply globalCFT_localAlgebraMapUnits_injective (hu w)
    rw [← hφ x w, ← hy, Idele.principalIdele_apply,
      globalCFT_principalIdele_localAlgebraMapUnits u hu φ hφ a w, ha]
  rw [hx]
  exact (QuotientGroup.eq_one_iff (Idele.principalIdele K a)).mpr ⟨a, rfl⟩

end NK.GlobalCFT.Inclusion

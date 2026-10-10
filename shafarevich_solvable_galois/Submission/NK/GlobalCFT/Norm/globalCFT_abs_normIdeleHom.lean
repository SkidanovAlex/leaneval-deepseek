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
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.GlobalCFT.Norm.globalCFT_localAbs_localNormInfinite
import Submission.NK.GlobalCFT.NormFunctorial

/-!
# The content of the norm of an idèle

For a finite extension `L / K` of number fields and an idèle `x` of `L`, the **content** (the
normalized absolute value) of the idèlic norm equals the content of `x`:

`|N_{L/K} x|_K = |x|_L`,  i.e. `Idele.abs K (Idele.normIdeleHom K L x) = Idele.abs L x`.

This is the compatibility of the idèlic norm with the content homomorphism `𝕀 K →* ℝˣ`; it is
the statement that the norm map on idèles preserves the norm-one subgroups `𝕀¹`.

## Strategy

Writing `abs K y = ∏ᶠ_v |y_v|_v` as a finitary product of the normalized local absolute values,
the identity follows by comparing the two products place by place.  The two local inputs are

* `globalCFT_localAbs_localNormFinite`: at a finite place, `v x` is multiplied by the inertia
  degree `f` under the local norm (`globalCFT_val_norm_adicCompletion_eq_pow_inertiaDeg`), which
  is exactly the change of normalization between `toNNReal` at a prime and at a prime above it
  (`toNNReal_absNorm_pow`);
* `globalCFT_localAbs_localNormInfinite`: at an infinite place (proved by the sibling module
  `NK.GlobalCFT.Norm.globalCFT_localAbs_localNormInfinite`), where the local fields are `ℝ`
  and `ℂ`.

The global comparison then uses the fibration of the places of `L` over the places of `K`
(`globalCFT_placeUnder`, `globalCFT_fiberPlaces`) together with
`Finset.prod_fiberwise_of_maps_to` (in the form `finprod_prod_filter`).

## Main result

* `NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct WithZero NNReal
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace NK.GlobalCFT.Norm

section Helpers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- In the value group `ℤᵐ⁰`, the `e`-th power map is injective on nonzero elements. -/
theorem withZero_pow_left_cancel' {e : ℕ} (he : e ≠ 0)
    {a b : WithZero (Multiplicative ℤ)} (hb : b ≠ 0) (h : a ^ e = b ^ e) : a = b := by
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_pow he] at h
    exact (pow_ne_zero e hb) h.symm
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨WithZero.log a, WithZero.exp_log ha⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, WithZero.exp n = b := ⟨WithZero.log b, WithZero.exp_log hb⟩
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul, nsmul_eq_mul] at h
  rw [WithZero.exp_inj]
  exact mul_left_cancel₀ (show (e : ℤ) ≠ 0 from by exact_mod_cast he) h

/-- The local norm multiplies valuations by the inertia degree. -/
theorem globalCFT_val_norm_adicCompletion_eq_pow_inertiaDeg
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ x : (q.adicCompletion L)ˣ,
      Valued.v (Algebra.norm (Q.adicCompletion K) (x : q.adicCompletion L)) =
        (Valued.v (x : q.adicCompletion L)) ^ (q.asIdeal.inertiaDeg (𝓞 K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hIC : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension Q q hq
  have hnorm_int : ∀ y : q.adicCompletion L, y ∈ q.adicCompletionIntegers L →
      Algebra.norm (Q.adicCompletion K) y ∈ Q.adicCompletionIntegers K := by
    intro y hy
    have hint : IsIntegral (Q.adicCompletionIntegers K) y :=
      (IsIntegralClosure.isIntegral_iff (A := q.adicCompletionIntegers L)
        (R := Q.adicCompletionIntegers K) (B := q.adicCompletion L) (x := y)).mpr
        ⟨⟨y, hy⟩, rfl⟩
    have h2 := Algebra.isIntegral_norm (Q.adicCompletion K) hint
    obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := Q.adicCompletionIntegers K)
      (R := Q.adicCompletionIntegers K) (B := Q.adicCompletion K)
      (x := Algebra.norm (Q.adicCompletion K) y)).mp h2
    exact hz ▸ z.2
  have hnorm_unit : ∀ y : q.adicCompletion L, Valued.v y = 1 →
      Valued.v (Algebra.norm (Q.adicCompletion K) y) = 1 := by
    intro y hy
    have hyne : y ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp (by rw [hy]; exact one_ne_zero)
    have hmem : y ∈ q.adicCompletionIntegers L :=
      (mem_adicCompletionIntegers (𝓞 L) L q).mpr (le_of_eq hy)
    have hmem' : y⁻¹ ∈ q.adicCompletionIntegers L := by
      rw [mem_adicCompletionIntegers (𝓞 L) L q, map_inv₀, hy]
      exact le_refl 1
    have h1 : Valued.v (Algebra.norm (Q.adicCompletion K) y) ≤ 1 :=
      (mem_adicCompletionIntegers (𝓞 K) K Q).mp (hnorm_int y hmem)
    have h2 : Valued.v (Algebra.norm (Q.adicCompletion K) y⁻¹) ≤ 1 :=
      (mem_adicCompletionIntegers (𝓞 K) K Q).mp (hnorm_int y⁻¹ hmem')
    have hprod : Valued.v (Algebra.norm (Q.adicCompletion K) y) *
        Valued.v (Algebra.norm (Q.adicCompletion K) y⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hyne]
      simp
    have hge : (1 : ℤᵐ⁰) ≤ Valued.v (Algebra.norm (Q.adicCompletion K) y) :=
      calc (1 : ℤᵐ⁰) = Valued.v (Algebra.norm (Q.adicCompletion K) y) *
            Valued.v (Algebra.norm (Q.adicCompletion K) y⁻¹) := hprod.symm
        _ ≤ Valued.v (Algebra.norm (Q.adicCompletion K) y) * 1 := mul_le_mul_right h2 _
        _ = Valued.v (Algebra.norm (Q.adicCompletion K) y) := mul_one _
    exact le_antisymm h1 hge
  have halg : (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) =
      Commons.RingTheory.Henselian.adicCompletionMap Q q hq :=
    RingHom.algebraMap_toAlgebra _
  have hkey : ∀ π : q.adicCompletionIntegers L,
      Valued.v (π : q.adicCompletion L) = (WithZero.exp (-1) : ℤᵐ⁰) →
      Valued.v (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L)) =
        (WithZero.exp (-1) : ℤᵐ⁰) ^ (q.asIdeal.inertiaDeg (𝓞 K)) := by
    intro π hπval
    obtain ⟨ϖ, hϖval, -⟩ :=
      Commons.NumberTheory.NumberField.Completion.exists_uniformizer_adicCompletionIntegers (K := K) Q
    have hπne : (π : q.adicCompletion L) ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (by rw [hπval]; exact WithZero.exp_ne_zero)
    set e := q.asIdeal.ramificationIdx (𝓞 K) with he
    set f := q.asIdeal.inertiaDeg (𝓞 K) with hf
    have he0 : e ≠ 0 := by
      rw [he]
      exact (Ideal.ramificationIdx_pos (q := q.asIdeal) (𝓞 K)).ne'
    have hn : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) = e * f := by
      rw [he, hf]
      exact (Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        Q q hq).symm
    set u : q.adicCompletion L :=
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) (ϖ : Q.adicCompletion K) *
        ((π : q.adicCompletion L) ^ e)⁻¹ with hu
    have hvalπe : Valued.v ((π : q.adicCompletion L) ^ e) = (WithZero.exp (-1) : ℤᵐ⁰) ^ e := by
      rw [Valuation.map_pow, hπval]
    have hvalalg : Valued.v ((algebraMap (Q.adicCompletion K) (q.adicCompletion L))
        (ϖ : Q.adicCompletion K)) = (WithZero.exp (-1) : ℤᵐ⁰) ^ e := by
      rw [halg,
        Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq
          (ϖ : Q.adicCompletion K), hϖval, ← he]
    have huval : Valued.v u = 1 := by
      rw [hu, map_mul, map_inv₀, hvalalg, hvalπe,
        mul_inv_cancel₀ (pow_ne_zero e (WithZero.exp_ne_zero))]
    have hsplit : (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) (ϖ : Q.adicCompletion K) =
        (π : q.adicCompletion L) ^ e * u := by
      rw [hu, ← mul_assoc, mul_comm ((π : q.adicCompletion L) ^ e), mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero e hπne), mul_one]
    have hnormsplit : Algebra.norm (Q.adicCompletion K)
          ((algebraMap (Q.adicCompletion K) (q.adicCompletion L)) (ϖ : Q.adicCompletion K)) =
        (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L)) ^ e *
          Algebra.norm (Q.adicCompletion K) u := by
      rw [hsplit, map_mul, map_pow]
    have hLHS : Valued.v (Algebra.norm (Q.adicCompletion K)
        ((algebraMap (Q.adicCompletion K) (q.adicCompletion L)) (ϖ : Q.adicCompletion K))) =
        (WithZero.exp (-1) : ℤᵐ⁰) ^ (e * f) := by
      rw [Algebra.norm_algebraMap, Valuation.map_pow, hϖval, hn]
    have heq : (Valued.v (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L))) ^ e =
        ((WithZero.exp (-1) : ℤᵐ⁰) ^ f) ^ e := by
      have h1 : Valued.v (Algebra.norm (Q.adicCompletion K)
            ((algebraMap (Q.adicCompletion K) (q.adicCompletion L)) (ϖ : Q.adicCompletion K))) =
          (Valued.v (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L))) ^ e := by
        rw [hnormsplit, map_mul, map_pow, hnorm_unit u huval, mul_one]
      rw [← h1, hLHS, mul_comm e f, pow_mul]
    exact withZero_pow_left_cancel' he0 (pow_ne_zero f WithZero.exp_ne_zero) heq
  intro x
  obtain ⟨π, hπval, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_adicCompletionIntegers (K := L) q
  have hπkey := hkey π hπval
  set f := q.asIdeal.inertiaDeg (𝓞 K) with hf
  have hπne : (π : q.adicCompletion L) ≠ 0 :=
    (Valuation.ne_zero_iff Valued.v).mp (by rw [hπval]; exact WithZero.exp_ne_zero)
  set m : ℤ := WithZero.log (Valued.v (x : q.adicCompletion L)) with hm
  have hvxne : Valued.v (x : q.adicCompletion L) ≠ 0 :=
    (Valuation.ne_zero_iff Valued.v).mpr (Units.ne_zero x)
  have hexpm : Valued.v (x : q.adicCompletion L) = WithZero.exp m := (WithZero.exp_log hvxne).symm
  set y : q.adicCompletion L := (x : q.adicCompletion L) * (π : q.adicCompletion L) ^ m with hy
  have hvaly : Valued.v y = 1 := by
    rw [hy, map_mul, hexpm, map_zpow₀, hπval, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      show m + m • (-1 : ℤ) = 0 by ring, WithZero.exp_zero]
  have hNπ : Valued.v (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L)) =
      (WithZero.exp (-1) : ℤᵐ⁰) ^ f := hπkey
  have hxsplit : (x : q.adicCompletion L) = y * (π : q.adicCompletion L) ^ (-m) := by
    rw [hy, mul_assoc, ← zpow_add₀ hπne m (-m), add_neg_cancel, zpow_zero, mul_one]
  have hnormx : Algebra.norm (Q.adicCompletion K) (x : q.adicCompletion L) =
      Algebra.norm (Q.adicCompletion K) y *
        (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L)) ^ (-m) := by
    rw [hxsplit, map_mul, Algebra.norm_zpow]
  rw [hnormx, map_mul, hnorm_unit y hvaly, one_mul, map_zpow₀, hNπ, hexpm]
  rw [← WithZero.exp_nsmul, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul]
  congr 1
  ring



open WithZeroMulInt

/-- Base change for `WithZeroMulInt.toNNReal`: if `e' = e ^ k` with `k ≠ 0`, then `toNNReal`
at `e'` is the `k`-th power of `toNNReal` at `e`. -/
theorem toNNReal_eq_pow_of_base {e e' : ℝ≥0} (he : e ≠ 0) (he' : e' ≠ 0) {k : ℕ}
    (hk : k ≠ 0) (hbase : e' = e ^ k) (z : ℤᵐ⁰) :
    toNNReal he (z ^ k) = toNNReal he' z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [zero_pow hk, map_zero, map_zero]
  · rw [map_pow, toNNReal_neg_apply he hz, toNNReal_neg_apply he' hz, hbase,
      ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]

/-- The `toNNReal` normalizations at a prime and at a prime above it differ by the inertia
degree: `toNNReal` at `q` is `toNNReal` at `Q` raised to the `f`. -/
theorem toNNReal_absNorm_pow (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (z : ℤᵐ⁰) :
    toNNReal (HeightOneSpectrum.absNorm_ne_zero Q) (z ^ q.asIdeal.inertiaDeg (𝓞 K)) =
      toNNReal (HeightOneSpectrum.absNorm_ne_zero q) z := by
  have hbase : ((Ideal.absNorm q.asIdeal : ℕ) : ℝ≥0) =
      ((Ideal.absNorm Q.asIdeal : ℕ) : ℝ≥0) ^ q.asIdeal.inertiaDeg (𝓞 K) := by
    rw [← Ideal.absNorm_pow_inertiaDeg (R := 𝓞 K) (S := 𝓞 L) Q.asIdeal q.asIdeal,
      Nat.cast_pow]
  exact toNNReal_eq_pow_of_base (HeightOneSpectrum.absNorm_ne_zero Q)
    (HeightOneSpectrum.absNorm_ne_zero q)
    (Ideal.inertiaDeg_pos q.asIdeal (𝓞 K)).ne' hbase z

/-- **The local compatibility of the content with the local norm at a finite place.** -/
theorem globalCFT_localAbs_localNormFinite (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (y : (q.adicCompletion L)ˣ) :
    Idele.localAbs K (Place.ofFinite Q) (Place.localNormFinite q Q hq y) =
      Idele.localAbs L (Place.ofFinite q) y := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  rw [show Place.localNormFinite q Q hq =
      Units.map (Algebra.norm (Q.adicCompletion K)) from rfl]
  rw [Idele.localAbs_ofFinite, Idele.localAbs_ofFinite]
  apply Units.ext
  simp only [Units.coe_map, Units.val_mk0]
  rw [NumberField.FinitePlace.norm_def (v := Q) (x := Algebra.norm (Q.adicCompletion K)
        (y : q.adicCompletion L)),
    NumberField.FinitePlace.norm_def (v := q) (x := (y : q.adicCompletion L))]
  rw [globalCFT_val_norm_adicCompletion_eq_pow_inertiaDeg Q q hq y]
  exact congrArg _ (toNNReal_absNorm_pow Q q hq (Valued.v (y : q.adicCompletion L)))


/-! ## The place of `K` below a place of `L`, and the fibres -/

/-- A choice of the place of `K` below a given place of `L`. -/
noncomputable def globalCFT_placeUnder (w : Place L) : Place K :=
  Classical.choose (Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)

theorem liesOver_globalCFT_placeUnder (w : Place L) :
    Place.LiesOver w (globalCFT_placeUnder (K := K) (L := L) w) :=
  Classical.choose_spec (Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)

/-- The places of `L` above a given place of `K`, as a finset. -/
noncomputable def globalCFT_fiberPlaces (v : Place K) : Finset (Place L) :=
  match v with
  | Sum.inl v' => (Place.fiberInfinite (K := K) (L := L) v').map
      ⟨Place.ofInfinite, fun _ _ h => Place.ofInfinite_inj.mp h⟩
  | Sum.inr Q => (Place.primesOverFinite (K := K) (L := L) Q).map
      ⟨Place.ofFinite, fun _ _ h => Place.ofFinite_inj.mp h⟩

theorem mem_globalCFT_fiberPlaces {v : Place K} {w : Place L} :
    w ∈ globalCFT_fiberPlaces (K := K) (L := L) v ↔ Place.LiesOver w v := by
  cases v with
  | inl v' =>
    constructor
    · intro hw
      obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
      exact Place.liesOver_ofInfinite ((Place.mem_fiberInfinite).mp hw')
    · intro hw
      rcases hw with ⟨w', v'', hw', hv', hLies⟩ | ⟨q', Q', hw', hv', hLies⟩
      · have hvv : v' = v'' := Place.ofInfinite_inj.mp hv'
        rw [hw']
        exact Finset.mem_map.mpr ⟨w', (Place.mem_fiberInfinite).mpr (hvv.symm ▸ hLies), rfl⟩
      · exact absurd hv' (Place.ofInfinite_ne_ofFinite v' Q')
  | inr Q =>
    constructor
    · intro hw
      obtain ⟨q', hq', rfl⟩ := Finset.mem_map.mp hw
      exact Place.liesOver_ofFinite ((Place.mem_primesOverFinite).mp hq')
    · intro hw
      rcases hw with ⟨w', v'', hw', hv', hLies⟩ | ⟨q', Q', hw', hv', hLies⟩
      · exact absurd hv' (Place.ofInfinite_ne_ofFinite v'' Q).symm
      · have hQQ : Q = Q' := Place.ofFinite_inj.mp hv'
        rw [hw']
        exact Finset.mem_map.mpr ⟨q', (Place.mem_primesOverFinite).mpr (hQQ.symm ▸ hLies), rfl⟩

/-! ## The content of the norm of an idèle -/

end Helpers

theorem globalCFT_abs_normIdeleHom {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (x : 𝕀[L]) :
    Idele.abs K (Idele.normIdeleHom K L x) = Idele.abs L x := by
  classical
  set f : Place L → ℝˣ := fun w => Idele.localAbs L w (x w) with hf
  have hf_fin : (Function.mulSupport f).Finite := by
    have h := Idele.localAbs_eq_one_eventually (K := L) x
    rw [Filter.eventually_cofinite] at h
    simpa [f, Function.mulSupport] using h
  obtain ⟨S, hSsub⟩ : ∃ S : Finset (Place L), Function.mulSupport f ⊆ (S : Set (Place L)) :=
    ⟨hf_fin.toFinset, fun w hw => by simpa using hw⟩
  have hSout : ∀ w : Place L, w ∉ S → f w = 1 := fun w hw => by
    by_contra h
    exact hw (hSsub (by simpa [Function.mulSupport] using h))
  have hterm : ∀ v : Place K,
      Idele.localAbs K v ((Idele.normIdeleHom K L x) v) =
        ∏ w ∈ S.filter (fun w => globalCFT_placeUnder (K := K) (L := L) w = v), f w := by
    intro v
    rw [Idele.normIdeleHom_apply]
    have hfiber : Idele.localAbs K v (Idele.normIdeleFun K L x v) =
        ∏ w ∈ globalCFT_fiberPlaces (K := K) (L := L) v, f w := by
      cases v with
      | inl v' =>
        rw [Idele.normIdeleFun_ofInfinite, map_prod]
        have hfac : (∏ w' ∈ (Place.fiberInfinite (K := K) (L := L) v').attach,
            (letI : (w'.1 : InfinitePlace L).LiesOver v' := (Place.mem_fiberInfinite).mp w'.2
             (Idele.localAbs K (Place.ofInfinite v'))
               (Place.localNormInfinite w'.1 v' (x (Place.ofInfinite w'.1)))))
            = ∏ w' ∈ (Place.fiberInfinite (K := K) (L := L) v').attach, f (Place.ofInfinite w'.1) :=
          Finset.prod_congr rfl (fun w' _ => globalCFT_localAbs_localNormInfinite v' w'.1
            ((Place.mem_fiberInfinite).mp w'.2) (x (Place.ofInfinite w'.1)))
        rw [hfac, show (∏ w' ∈ (Place.fiberInfinite (K := K) (L := L) v').attach,
              f (Place.ofInfinite w'.1)) =
            ∏ w' ∈ (Place.fiberInfinite (K := K) (L := L) v').attach,
              (f ∘ Place.ofInfinite) w'.1 from rfl,
          Finset.prod_attach]
        exact (Finset.prod_map _ ⟨Place.ofInfinite, fun _ _ h => Place.ofInfinite_inj.mp h⟩ f).symm
      | inr Q =>
        rw [Idele.normIdeleFun_ofFinite, map_prod]
        have hfac : (∏ q' ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
            (letI : q'.1.asIdeal.LiesOver Q.asIdeal := (Place.mem_primesOverFinite).mp q'.2
             (Idele.localAbs K (Place.ofFinite Q))
               (Place.localNormFinite q'.1 Q (Place.mem_primesOverFinite.mp q'.2)
                 (x (Place.ofFinite q'.1)))))
            = ∏ q' ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach, f (Place.ofFinite q'.1) :=
          Finset.prod_congr rfl (fun q' _ => globalCFT_localAbs_localNormFinite Q q'.1
            ((Place.mem_primesOverFinite).mp q'.2) (x (Place.ofFinite q'.1)))
        rw [hfac, show (∏ q' ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
              f (Place.ofFinite q'.1)) =
            ∏ q' ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
              (f ∘ Place.ofFinite) q'.1 from rfl,
          Finset.prod_attach]
        exact (Finset.prod_map _ ⟨Place.ofFinite, fun _ _ h => Place.ofFinite_inj.mp h⟩ f).symm
    rw [hfiber]
    exact (Finset.prod_subset
      (fun w hw => (mem_globalCFT_fiberPlaces (K := K) (L := L) (v := v) (w := w)).mpr (by
        have h1 : globalCFT_placeUnder (K := K) (L := L) w = v := (Finset.mem_filter.mp hw).2
        rw [← h1]
        exact liesOver_globalCFT_placeUnder w))
      (fun w hw hw' => by
        by_cases hwS : w ∈ S
        · refine absurd (Finset.mem_filter.mpr ⟨hwS, ?_⟩) hw'
          exact Inclusion.globalCFT_liesOver_unique (liesOver_globalCFT_placeUnder w)
            ((mem_globalCFT_fiberPlaces (K := K) (L := L) (v := v) (w := w)).mp hw)
        · exact hSout w hwS)).symm
  rw [Idele.abs_apply, Idele.abs_apply]
  calc ∏ᶠ v : Place K, Idele.localAbs K v ((Idele.normIdeleHom K L x) v)
      = ∏ᶠ v : Place K,
          ∏ w ∈ S.filter (fun w => globalCFT_placeUnder (K := K) (L := L) w = v), f w :=
        finprod_congr hterm
    _ = ∏ w ∈ S, f w := finprod_prod_filter (globalCFT_placeUnder (K := K) (L := L)) S f
    _ = ∏ᶠ w : Place L, f w := (finprod_eq_prod_of_mulSupport_subset f hSsub).symm
    _ = ∏ᶠ w : Place L, Idele.localAbs L w (x w) := by
        refine finprod_congr (fun w => ?_); rfl

end NK.GlobalCFT.Norm

end

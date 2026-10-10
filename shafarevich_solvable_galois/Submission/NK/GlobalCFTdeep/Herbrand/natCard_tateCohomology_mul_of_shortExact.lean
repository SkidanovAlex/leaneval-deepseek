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
import Submission.NK.GlobalCFTdeep.Herbrand.PeriodicComplex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
open CategoryTheory

noncomputable section
namespace NK.GlobalCFTdeep.Herbrand

/-- **The arithmetic of the Tate hexagon.** -/
theorem cyclicExact_card_relation
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ A'] [Module ℤ B'] [Module ℤ C']
    (α : A →ₗ[ℤ] B) (β : B →ₗ[ℤ] C) (γ : C →ₗ[ℤ] A')
    (δ : A' →ₗ[ℤ] B') (ε : B' →ₗ[ℤ] C') (ζ : C' →ₗ[ℤ] A)
    (hαβ : LinearMap.range α = LinearMap.ker β) (hβγ : LinearMap.range β = LinearMap.ker γ)
    (hγδ : LinearMap.range γ = LinearMap.ker δ) (hδε : LinearMap.range δ = LinearMap.ker ε)
    (hεζ : LinearMap.range ε = LinearMap.ker ζ) (hζα : LinearMap.range ζ = LinearMap.ker α) :
    Nat.card B * Nat.card A' * Nat.card C' = Nat.card A * Nat.card C * Nat.card B' := by
  have hB : Nat.card B = Nat.card ↥(LinearMap.range α) * Nat.card ↥(LinearMap.range β) := by
    have hcard : Nat.card B = Nat.card ↥(LinearMap.ker β) * Nat.card (B ⧸ LinearMap.ker β) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange β).toEquiv] at hcard
    rw [hcard, ← hαβ]
  have hA' : Nat.card A' = Nat.card ↥(LinearMap.range γ) * Nat.card ↥(LinearMap.range δ) := by
    have hcard : Nat.card A' = Nat.card ↥(LinearMap.ker δ) * Nat.card (A' ⧸ LinearMap.ker δ) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange δ).toEquiv] at hcard
    rw [hcard, ← hγδ]
  have hC' : Nat.card C' = Nat.card ↥(LinearMap.range ε) * Nat.card ↥(LinearMap.range ζ) := by
    have hcard : Nat.card C' = Nat.card ↥(LinearMap.ker ζ) * Nat.card (C' ⧸ LinearMap.ker ζ) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange ζ).toEquiv] at hcard
    rw [hcard, ← hεζ]
  have hA : Nat.card A = Nat.card ↥(LinearMap.range ζ) * Nat.card ↥(LinearMap.range α) := by
    have hcard : Nat.card A = Nat.card ↥(LinearMap.ker α) * Nat.card (A ⧸ LinearMap.ker α) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange α).toEquiv] at hcard
    rw [hcard, ← hζα]
  have hC : Nat.card C = Nat.card ↥(LinearMap.range γ) * Nat.card ↥(LinearMap.range β) := by
    have hcard : Nat.card C = Nat.card ↥(LinearMap.ker γ) * Nat.card (C ⧸ LinearMap.ker γ) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange γ).toEquiv] at hcard
    rw [hcard, ← hβγ]; ring
  have hB' : Nat.card B' = Nat.card ↥(LinearMap.range δ) * Nat.card ↥(LinearMap.range ε) := by
    have hcard : Nat.card B' = Nat.card ↥(LinearMap.ker ε) * Nat.card (B' ⧸ LinearMap.ker ε) :=
      Submodule.card_eq_card_quotient_mul_card _
    rw [Nat.card_congr (LinearMap.quotKerEquivRange ε).toEquiv] at hcard
    rw [hcard, ← hδε]
  rw [hB, hA', hC', hA, hC, hB']
  ring

section Bridge
variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G] (g : G)

noncomputable def perF_homology_two_iso (M : Rep k G) :
    ((perF (k:=k) (G:=G) g).obj M).homology 2 ≅
      (Rep.FiniteCyclicGroup.normHomCompSub M g).homology :=
  HomologicalComplex.alternatingConstHomologyIsoEven (ModuleCat.of k M.V)
    (φ := ModuleCat.ofHom (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap)
    (ψ := ModuleCat.ofHom M.norm.hom.toLinearMap)
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun i j hij => ComplexShape.up_nat_odd_add hij)
    (by simp) (by simp) (by norm_num : Even 2)

noncomputable def perF_homology_one_iso (M : Rep k G) :
    ((perF (k:=k) (G:=G) g).obj M).homology 1 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom M g).homology :=
  HomologicalComplex.alternatingConstHomologyIsoOdd (ModuleCat.of k M.V)
    (φ := ModuleCat.ofHom (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap)
    (ψ := ModuleCat.ofHom M.norm.hom.toLinearMap)
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun i j hij => ComplexShape.up_nat_odd_add hij)
    (by simp) (by simp) (by norm_num : Odd 1)

noncomputable def perF_homology_three_iso (M : Rep k G) :
    ((perF (k:=k) (G:=G) g).obj M).homology 3 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom M g).homology :=
  HomologicalComplex.alternatingConstHomologyIsoOdd (ModuleCat.of k M.V)
    (φ := ModuleCat.ofHom (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap)
    (ψ := ModuleCat.ofHom M.norm.hom.toLinearMap)
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun i j hij => ComplexShape.up_nat_odd_add hij)
    (by simp) (by simp) (by norm_num : Odd 3)

end Bridge

section PeriodicIso
variable {G : Type} [CommGroup G] [Fintype G]

/-- The identity-component isomorphism `K.sc 2 ≅ K.sc 4` of the periodic complex. -/
noncomputable def scIso (g : G) (M : Rep ℤ G) :
    ((perF (k:=ℤ) (G:=G) g).obj M).sc 2 ≅ ((perF (k:=ℤ) (G:=G) g).obj M).sc 4 := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ <;>
    simp only [perF, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor', CochainComplex.prev_nat_succ, CochainComplex.next,
      Nat.reduceAdd, Rep.FiniteCyclicGroup.moduleCatCochainComplex,
      HomologicalComplex.alternatingConst, Iso.refl_hom, Category.id_comp, Category.comp_id] <;>
    norm_num

lemma scIso_natural (g : G) {M M' : Rep ℤ G} (ψ : M ⟶ M') :
    (scIso g M).hom ≫
        (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) 4).map
          ((perF (k:=ℤ) (G:=G) g).map ψ)
      = (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) 2).map
          ((perF (k:=ℤ) (G:=G) g).map ψ) ≫ (scIso g M').hom := by
  apply ShortComplex.hom_ext <;> rfl

/-- The periodicity isomorphism between the homology in degrees `2` and `4`. -/
noncomputable def perIso (g : G) (M : Rep ℤ G) :
    ((perF (k:=ℤ) (G:=G) g).obj M).homology 2 ≅
      ((perF (k:=ℤ) (G:=G) g).obj M).homology 4 :=
  ShortComplex.homologyMapIso (scIso g M)

lemma perIso_natural (g : G) {M M' : Rep ℤ G} (ψ : M ⟶ M') :
    (perIso g M).hom ≫ HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map ψ) 4
      = HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map ψ) 2 ≫ (perIso g M').hom := by
  have h := scIso_natural g ψ
  simp only [perIso, ShortComplex.homologyMapIso_hom, HomologicalComplex.homologyMap] at h ⊢
  erw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  exact congrArg (fun t => ShortComplex.homologyMap t) h

end PeriodicIso

section ZBridge
variable {G : Type} [CommGroup G] [Fintype G] (g : G)

theorem natCard_perF_homology_two_eq (M : Rep ℤ G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 2) = Nat.card ↥(tateCohomology M 0) := by
  calc Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 2)
      = Nat.card ↥((Rep.FiniteCyclicGroup.normHomCompSub M g).homology) :=
        Nat.card_congr (perF_homology_two_iso (k := ℤ) g M).toLinearEquiv.toEquiv
    _ = Nat.card ↥(groupCohomology M 2) :=
        (Nat.card_congr (Rep.FiniteCyclicGroup.groupCohomologyIsoEven M g hg 2
          (by norm_num : Even 2)).toLinearEquiv.toEquiv).symm
    _ = Nat.card ↥(tateCohomology M 0) :=
        Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic_general M g hg

theorem natCard_perF_homology_one_eq (M : Rep ℤ G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 1) = Nat.card ↥(tateCohomology M 1) := by
  calc Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 1)
      = Nat.card ↥((Rep.FiniteCyclicGroup.subCompNormHom M g).homology) :=
        Nat.card_congr (perF_homology_one_iso (k := ℤ) g M).toLinearEquiv.toEquiv
    _ = Nat.card ↥(groupCohomology M 1) :=
        (Nat.card_congr (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd M g hg 1
          (by norm_num : Odd 1)).toLinearEquiv.toEquiv).symm
    _ = Nat.card ↥(tateCohomology M 1) :=
        (Nat.card_congr ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M).toLinearEquiv.toEquiv).symm

theorem natCard_perF_homology_three_eq (M : Rep ℤ G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 3) = Nat.card ↥(tateCohomology M 1) := by
  calc Nat.card ↥(((perF (k:=ℤ) (G:=G) g).obj M).homology 3)
      = Nat.card ↥((Rep.FiniteCyclicGroup.subCompNormHom M g).homology) :=
        Nat.card_congr (perF_homology_three_iso (k := ℤ) g M).toLinearEquiv.toEquiv
    _ = Nat.card ↥(groupCohomology M 1) :=
        (Nat.card_congr (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd M g hg 1
          (by norm_num : Odd 1)).toLinearEquiv.toEquiv).symm
    _ = Nat.card ↥(tateCohomology M 1) :=
        (Nat.card_congr ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M).toLinearEquiv.toEquiv).symm

end ZBridge


section Zeta
variable {G : Type} [CommGroup G] [Fintype G]

/-- The wrapped connecting map `Ĥ¹(X₃) → Ĥ⁰(X₁)` obtained by composing the connecting map
`Ĥ¹(X₃) → Ĥ²(X₁)` with the (inverse) periodicity isomorphism `Ĥ²(X₁) ≅ Ĥ⁰(X₁)`. -/
noncomputable def perZeta (g : G) (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    (h34 : (ComplexShape.up ℕ).Rel 3 4) :
    ↥(((perF (k:=ℤ) (G:=G) g).obj S.X₃).homology 3) →ₗ[ℤ]
      ↥(((perF (k:=ℤ) (G:=G) g).obj S.X₁).homology 2) :=
  (perIso g S.X₁).inv.hom.comp ((perF_shortExact (k:=ℤ) (G:=G) g S hS).δ 3 4 h34).hom

lemma perZeta_apply (g : G) (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    (h34 : (ComplexShape.up ℕ).Rel 3 4)
    (x : ↥(((perF (k:=ℤ) (G:=G) g).obj S.X₃).homology 3)) :
    perZeta (G := G) g S hS h34 x
      = (perIso g S.X₁).inv (((perF_shortExact (k:=ℤ) (G:=G) g S hS).δ 3 4 h34).hom x) :=
  rfl

lemma perIso_hom_injective (g : G) (M : Rep ℤ G) :
    Function.Injective (perIso g M).hom := by
  intro a b h
  have := congrArg (fun z => (perIso g M).inv z) h
  simpa only [Iso.hom_inv_id_apply] using this

end Zeta

theorem natCard_tateCohomology_mul_of_shortExact {G : Type} [CommGroup G] [Fintype G] [IsCyclic G]
    (S : CategoryTheory.ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    [Finite ↥(tateCohomology S.X₁ 0)] [Finite ↥(tateCohomology S.X₁ 1)]
    [Finite ↥(tateCohomology S.X₂ 0)] [Finite ↥(tateCohomology S.X₂ 1)]
    [Finite ↥(tateCohomology S.X₃ 0)] [Finite ↥(tateCohomology S.X₃ 1)] :
    Nat.card ↥(tateCohomology S.X₂ 0) * Nat.card ↥(tateCohomology S.X₁ 1) *
        Nat.card ↥(tateCohomology S.X₃ 1)
      = Nat.card ↥(tateCohomology S.X₁ 0) * Nat.card ↥(tateCohomology S.X₃ 0) *
        Nat.card ↥(tateCohomology S.X₂ 1) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hper := perF_shortExact (k := ℤ) (G := G) g S hS
  have h23 : (ComplexShape.up ℕ).Rel 2 3 := by simp
  have h34 : (ComplexShape.up ℕ).Rel 3 4 := by simp
  have hαβ : LinearMap.range
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom
      = LinearMap.ker
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 2).hom :=
    (hper.homology_exact₂ 2).moduleCat_range_eq_ker
  have hβγ : LinearMap.range
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 2).hom
      = LinearMap.ker (hper.δ 2 3 h23).hom :=
    (hper.homology_exact₃ 2 3 h23).moduleCat_range_eq_ker
  have hγδ : LinearMap.range (hper.δ 2 3 h23).hom
      = LinearMap.ker
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 3).hom :=
    (hper.homology_exact₁ 2 3 h23).moduleCat_range_eq_ker
  have hδε : LinearMap.range
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 3).hom
      = LinearMap.ker
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 3).hom :=
    (hper.homology_exact₂ 3).moduleCat_range_eq_ker
  have hδ4 : LinearMap.range (hper.δ 3 4 h34).hom
      = LinearMap.ker
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 4).hom :=
    (hper.homology_exact₁ 3 4 h34).moduleCat_range_eq_ker
  have hεδ : LinearMap.range
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 3).hom
      = LinearMap.ker (hper.δ 3 4 h34).hom :=
    (hper.homology_exact₃ 3 4 h34).moduleCat_range_eq_ker
  -- pointwise naturality of the periodicity isomorphism
  have hnat : ∀ w : ↥(((perF (k:=ℤ) (G:=G) g).obj S.X₁).homology 2),
      (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 4).hom
          ((perIso g S.X₁).hom w)
      = (perIso g S.X₂).hom
          ((HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom w) := by
    intro w
    have h := perIso_natural (G := G) g S.f
    have h' := congrArg (fun (t : ((perF (k:=ℤ) (G:=G) g).obj S.X₁).homology 2 ⟶
        ((perF (k:=ℤ) (G:=G) g).obj S.X₂).homology 4) => t.hom w) h
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h'
  have hεζ : LinearMap.range
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 3).hom
      = LinearMap.ker (perZeta (G := G) g S hS h34) := by
    rw [hεδ]
    ext x
    change ((hper.δ 3 4 h34).hom x = 0) ↔
      ((perIso g S.X₁).inv ((hper.δ 3 4 h34).hom x) = 0)
    constructor
    · intro hx; rw [hx]; exact map_zero (ModuleCat.Hom.hom (perIso g S.X₁).inv)
    · intro hx
      have h1 : (perIso g S.X₁).hom ((perIso g S.X₁).inv ((hper.δ 3 4 h34).hom x))
          = (hper.δ 3 4 h34).hom x :=
        Iso.inv_hom_id_apply (perIso g S.X₁) ((hper.δ 3 4 h34).hom x)
      rw [← h1, hx]; exact map_zero (ModuleCat.Hom.hom (perIso g S.X₁).hom)
  have hζα : LinearMap.range (perZeta (G := G) g S hS h34)
      = LinearMap.ker
        (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom := by
    ext y
    change (∃ x, perZeta (G := G) g S hS h34 x = y) ↔
      ((HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom y = 0)
    constructor
    · rintro ⟨x, hx⟩
      have hx' : (perIso g S.X₁).inv ((hper.δ 3 4 h34).hom x) = y := hx
      have hEy : (hper.δ 3 4 h34).hom x = (perIso g S.X₁).hom y := by
        rw [← hx']
        exact (Iso.inv_hom_id_apply (perIso g S.X₁) ((hper.δ 3 4 h34).hom x)).symm
      have h4z : (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 4).hom
          ((hper.δ 3 4 h34).hom x) = 0 := by
        have hmem : ((hper.δ 3 4 h34).hom x) ∈
            LinearMap.ker (HomologicalComplex.homologyMap
              ((perF (k:=ℤ) (G:=G) g).map S.f) 4).hom := by
          rw [← hδ4]; exact LinearMap.mem_range_self _ x
        exact hmem
      have hkey := hnat y
      rw [← hEy] at hkey
      rw [h4z] at hkey
      have hfin : (perIso g S.X₂).hom
            ((HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom y)
          = (perIso g S.X₂).hom 0 := by
        rw [hkey.symm]; exact (map_zero (ModuleCat.Hom.hom (perIso g S.X₂).hom)).symm
      exact perIso_hom_injective g S.X₂ hfin
    · intro hy
      have h4y : (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 4).hom
          ((perIso g S.X₁).hom y) = 0 := by
        rw [hnat y, hy]; exact map_zero (ModuleCat.Hom.hom (perIso g S.X₂).hom)
      have hmem : (perIso g S.X₁).hom y ∈ LinearMap.range (hper.δ 3 4 h34).hom := by
        rw [hδ4]; exact h4y
      obtain ⟨x, hx⟩ := hmem
      refine ⟨x, ?_⟩
      change (perIso g S.X₁).inv ((hper.δ 3 4 h34).hom x) = y
      rw [hx]
      exact Iso.hom_inv_id_apply (perIso g S.X₁) y
  have key := cyclicExact_card_relation
    (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 2).hom
    (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 2).hom
    (hper.δ 2 3 h23).hom
    (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.f) 3).hom
    (HomologicalComplex.homologyMap ((perF (k:=ℤ) (G:=G) g).map S.g) 3).hom
    (perZeta (G := G) g S hS h34)
    hαβ hβγ hγδ hδε hεζ hζα
  rw [← natCard_perF_homology_two_eq (G := G) g S.X₂ hg,
      ← natCard_perF_homology_three_eq (G := G) g S.X₁ hg,
      ← natCard_perF_homology_three_eq (G := G) g S.X₃ hg,
      ← natCard_perF_homology_two_eq (G := G) g S.X₁ hg,
      ← natCard_perF_homology_two_eq (G := G) g S.X₃ hg,
      ← natCard_perF_homology_three_eq (G := G) g S.X₂ hg]
  exact key

end NK.GlobalCFTdeep.Herbrand

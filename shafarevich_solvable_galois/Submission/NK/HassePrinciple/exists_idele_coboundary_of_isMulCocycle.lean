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
import Submission.NK.HassePrinciple.IdeleCocycleLocal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.HassePrinciple

open NK.GlobalCFT

section Aux

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Orbit representatives of the places

For the construction of the splitting idèle we choose, for each place `v` of `L`, a place
`basePlace v` in the `Gal(L/K)`-orbit of `v` together with an element `orbitRep v` of `Gal(L/K)`
moving `basePlace v` to `v`.  The choice is made once and for all (using `Quotient.out` on the
orbit quotient), so that `basePlace` is constant on orbits: `basePlace (g • v) = basePlace v`.
-/

/-- A chosen representative of the `Gal(L/K)`-orbit of a place. -/
def basePlace (v : Place L) : Place L :=
  (Quotient.mk (α := Place L) (MulAction.orbitRel (L ≃ₐ[K] L) (Place L)) v).out

theorem basePlace_rel (v : Place L) :
    (MulAction.orbitRel (L ≃ₐ[K] L) (Place L)) (basePlace (K := K) v) v :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (α := Place L)
    (MulAction.orbitRel (L ≃ₐ[K] L) (Place L)) v))

/-- `basePlace` is constant on `Gal(L/K)`-orbits. -/
theorem basePlace_smul (g : L ≃ₐ[K] L) (v : Place L) :
    basePlace (K := K) (g • v) = basePlace (K := K) v := by
  have h : Quotient.mk (α := Place L) (MulAction.orbitRel (L ≃ₐ[K] L) (Place L)) (g • v) =
      Quotient.mk (α := Place L) (MulAction.orbitRel (L ≃ₐ[K] L) (Place L)) v :=
    Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩))
  simp only [basePlace]
  rw [h]

/-- The orbit of a place is finite. -/
theorem orbit_finite (b : Place L) : (MulAction.orbit (L ≃ₐ[K] L) b).Finite := by
  have h : MulAction.orbit (L ≃ₐ[K] L) b = Set.range (fun g : L ≃ₐ[K] L => g • b) := rfl
  rw [h]
  exact Set.finite_range _

theorem basePlace_exists (v : Place L) : ∃ g : L ≃ₐ[K] L, g • v = basePlace (K := K) v :=
  MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (basePlace_rel v))

/-- A Galois element moving `v` to the orbit representative of `v`. -/
noncomputable def orbitMove (v : Place L) : L ≃ₐ[K] L := Classical.choose (basePlace_exists v)

theorem orbitMove_spec (v : Place L) : orbitMove (K := K) v • v = basePlace (K := K) v := by
  show Classical.choose (basePlace_exists v) • v = basePlace (K := K) v
  exact Classical.choose_spec (basePlace_exists v)

/-- A Galois element moving the orbit representative of `v` to `v`. -/
noncomputable def orbitRep (v : Place L) : L ≃ₐ[K] L := (orbitMove (K := K) v)⁻¹

theorem orbitRep_spec (v : Place L) : orbitRep (K := K) v • basePlace (K := K) v = v := by
  rw [orbitRep, ← orbitMove_spec v, inv_smul_smul]

/-! ## Elementary transport lemmas

The local field `L_v` is a family of types indexed by the places, so comparing elements at
propositionally equal places involves transports.  The following lemmas record the few facts
about them that the main computation needs. -/

/-- Transport of units of local fields along an equality of places, as a function. -/
def castFun {a b : Place L} (h : a = b) : (Place.localField L a)ˣ → (Place.localField L b)ˣ :=
  fun x => h ▸ x

theorem cast_symm_cast {a b : Place L} (h : a = b) (z : (Place.localField L a)ˣ) :
    h.symm ▸ (h ▸ z) = z := by cases h; rfl

/-- Transports along two proofs of the same equality of places agree (proof irrelevance). -/
theorem eqRec_congr {α : Type*} {F : α → Type*} {a b : α} (h h' : a = b) (x : F a) :
    h ▸ x = h' ▸ x :=
  eq_of_heq ((eqRec_heq h x).trans (eqRec_heq h' x).symm)

theorem cast_cast {a b c : Place L} (h : a = b) (h' : b = c) (x : (Place.localField L a)ˣ) :
    h' ▸ (h ▸ x) = (h.trans h') ▸ x := by cases h; cases h'; rfl

theorem cast_mul {a b : Place L} (h : a = b) (x y : (Place.localField L a)ˣ) :
    h ▸ (x * y) = (h ▸ x) * (h ▸ y) := by cases h; rfl

/-- The action `actVal` commutes with transport of its argument in the place. -/
theorem actVal_cast {γ : L ≃ₐ[K] L} {a b : Place L} (h : a = b)
    (x : (Place.localField L a)ˣ) :
    actVal γ b (h ▸ x) = (congrArg (fun p => γ • p) h) ▸ actVal γ a x := by
  cases h; rfl

theorem mem_localUnits_of_eq {a b : Place L} (h : a = b) (x : (Place.localField L a)ˣ) :
    x ∈ Place.localUnits L a ↔ (h ▸ x) ∈ Place.localUnits L b := by cases h; rfl

/-- The value of `γ • x` at a place `V` with `γ • w = V`, in terms of `actVal`. -/
theorem smul_apply_eq_of_eq {γ : L ≃ₐ[K] L} {w V : Place L} (e : γ • w = V) (x : Idele L) :
    (γ • x) V = e ▸ actVal γ w (x w) :=
  (units_transport e (γ • x)).symm.trans
    (congrArg (fun z => e ▸ z) (smul_apply_smul_place γ w x))

theorem smul_onePlace_apply (g : L ≃ₐ[K] L) (w : Place L) (u : (Place.localField L w)ˣ) :
    (g • onePlace w u) (g • w) = actVal g w u := by
  rw [smul_apply_smul_place, onePlace_apply_self]

theorem smul_onePlace_apply_of_eq {g : L ≃ₐ[K] L} {w V : Place L}
    (e : g • w = V) (u : (Place.localField L w)ˣ) :
    (g • onePlace w u) V = e ▸ actVal g w u :=
  (units_transport e (g • onePlace w u)).symm.trans
    (congrArg (fun z => e ▸ z) (smul_onePlace_apply g w u))

theorem smul_onePlace_apply_ne {g : L ≃ₐ[K] L} {w V : Place L} (h : V ≠ g • w)
    (u : (Place.localField L w)ˣ) : (g • onePlace w u) V = 1 := by
  rw [Idele.smul_apply]
  have h' : g⁻¹ • V ≠ w := fun he => h (by rw [← he, smul_inv_smul])
  rw [onePlace_apply_ne h' u, map_one]

/-- A translate of `onePlace` has local units as components. -/
theorem smul_onePlace_mem_localUnits {g : L ≃ₐ[K] L} {w : Place L}
    {u : (Place.localField L w)ˣ} (hu : u ∈ Place.localUnits L w) (V : Place L) :
    (g • onePlace w u) V ∈ Place.localUnits L V := by
  by_cases h : V = g • w
  · rw [smul_onePlace_apply_of_eq h.symm u]
    exact (mem_localUnits_of_eq h.symm (actVal g w u)).mp
      ((Place.localRingEquiv_mem_localUnits g w u).mp hu)
  · rw [smul_onePlace_apply_ne h u]
    exact Subgroup.one_mem _

/-- The value of `actVal` on a stabiliser element, using the Hilbert 90 relation. -/
theorem actVal_stabilizer_eq_of {c : (L ≃ₐ[K] L) → Idele L} {w₀ : Place L}
    {u : (Place.localField L w₀)ˣ}
    (hu : ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) w₀,
      c σ.1 w₀ = Units.map (localAut w₀ σ).toMonoidHom u / u)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w₀) :
    actVal σ.1 w₀ u =
      (MulAction.mem_stabilizer_iff.mp σ.2).symm ▸ (c σ.1 w₀ * u) := by
  have hσ : σ.1 • w₀ = w₀ := MulAction.mem_stabilizer_iff.mp σ.2
  have h := actVal_stabilizer w₀ σ u
  have hmap : Units.map (localAut w₀ σ).toMonoidHom u = c σ.1 w₀ * u := by
    rw [hu σ, div_eq_mul_inv]
    group
  calc actVal σ.1 w₀ u = hσ.symm ▸ (hσ ▸ actVal σ.1 w₀ u) := (cast_symm_cast hσ _).symm
    _ = hσ.symm ▸ Units.map (localAut w₀ σ).toMonoidHom u := by rw [h]
    _ = hσ.symm ▸ (c σ.1 w₀ * u) := by rw [hmap]

theorem div_apply_idele {K' : Type} [Field K'] [NumberField K'] (x y : Idele K')
    (v : Place K') : (x / y) v = x v / y v := by simp [div_eq_mul_inv]

theorem smul_div_idele (g : L ≃ₐ[K] L) (x y : Idele L) : g • (x / y) = (g • x) / (g • y) := by
  show (MulDistribMulAction.toMulAut (L ≃ₐ[K] L) (Idele L) g) (x / y) = _
  rw [map_div]
  rfl

/-! ## The local computation

The heart of the proof: replacing the representative used at a place by another element mapping
the chosen base place to the same place changes the corresponding local contribution only by the
cocycle.  This is the computation in which Hilbert 90 for the decomposition group enters. -/

theorem component_eq_of_stabilizer {c : (L ≃ₐ[K] L) → Idele L} {w₀ : Place L}
    {u : (Place.localField L w₀)ˣ}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g)
    (hu : ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) w₀,
      c σ.1 w₀ = Units.map (localAut w₀ σ).toMonoidHom u / u)
    (γ : L ≃ₐ[K] L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w₀) {V : Place L}
    (e : γ • w₀ = V) :
    (((γ * σ.1) • onePlace w₀ u) / c (γ * σ.1)) V =
      ((γ • onePlace w₀ u) / c γ) V := by
  have hσ : σ.1 • w₀ = w₀ := MulAction.mem_stabilizer_iff.mp σ.2
  have e' : (γ * σ.1) • w₀ = V := by rw [mul_smul, hσ]; exact e
  let B : γ • (σ.1 • w₀) = (γ * σ.1) • w₀ := (mul_smul γ σ.1 w₀).symm
  let A : γ • w₀ = γ • (σ.1 • w₀) := congrArg (fun p => γ • p) hσ.symm
  let Y : γ • w₀ = V := A.trans (B.trans e')
  have key : e' ▸ actVal (γ * σ.1) w₀ u = (γ • c σ.1) V * (e ▸ actVal γ w₀ u) := by
    have h1 : e' ▸ actVal (γ * σ.1) w₀ u
        = (B.trans e') ▸ actVal γ (σ.1 • w₀) (actVal σ.1 w₀ u) :=
      (congrArg (castFun e') (actVal_comp γ σ.1 w₀ u)).trans (cast_cast B e' _)
    have h2 : (B.trans e') ▸ actVal γ (σ.1 • w₀) (actVal σ.1 w₀ u)
        = (B.trans e') ▸ actVal γ (σ.1 • w₀) (hσ.symm ▸ (c σ.1 w₀ * u)) :=
      congrArg (castFun (B.trans e'))
        (congrArg (fun z : (Place.localField L (σ.1 • w₀))ˣ => actVal γ (σ.1 • w₀) z)
          (actVal_stabilizer_eq_of hu σ))
    have h3 : (B.trans e') ▸ actVal γ (σ.1 • w₀) (hσ.symm ▸ (c σ.1 w₀ * u))
        = (B.trans e') ▸ (A ▸ actVal γ w₀ (c σ.1 w₀ * u)) :=
      congrArg (castFun (B.trans e')) (actVal_cast hσ.symm (c σ.1 w₀ * u))
    have h4 : (B.trans e') ▸ (A ▸ actVal γ w₀ (c σ.1 w₀ * u))
        = Y ▸ actVal γ w₀ (c σ.1 w₀ * u) := cast_cast A (B.trans e') _
    have h5 : Y ▸ actVal γ w₀ (c σ.1 w₀ * u)
        = Y ▸ (actVal γ w₀ (c σ.1 w₀) * actVal γ w₀ u) :=
      congrArg (castFun Y) (actVal_mul γ w₀ (c σ.1 w₀) u)
    have h6 : Y ▸ (actVal γ w₀ (c σ.1 w₀) * actVal γ w₀ u)
        = (Y ▸ actVal γ w₀ (c σ.1 w₀)) * (Y ▸ actVal γ w₀ u) := cast_mul Y _ _
    have h7 : Y ▸ actVal γ w₀ (c σ.1 w₀) = (γ • c σ.1) V :=
      (eqRec_congr (F := fun p => (Place.localField L p)ˣ) Y e (actVal γ w₀ (c σ.1 w₀))).trans
        (smul_apply_eq_of_eq e (c σ.1)).symm
    have h8 : Y ▸ actVal γ w₀ u = e ▸ actVal γ w₀ u :=
      eqRec_congr (F := fun p => (Place.localField L p)ˣ) Y e (actVal γ w₀ u)
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (by rw [h7, h8]))))))
  rw [div_apply_idele, div_apply_idele, smul_onePlace_apply_of_eq e' u,
    smul_onePlace_apply_of_eq e u,
    show c (γ * σ.1) V = (γ • c σ.1) V * c γ V by rw [hc γ σ.1, Idele.mul_apply],
    key, div_eq_div_iff_mul_eq_mul]
  rw [mul_comm ((γ • c σ.1) V) (e ▸ actVal γ w₀ u), mul_assoc]

/-! ## The splitting idèle -/

/-- The local contribution at a place: the local solution at the orbit representative,
transported to the place, divided by the cocycle. -/
noncomputable def localPiece {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (v : Place L) : Idele L :=
  (orbitRep (K := K) v) • onePlace (basePlace (K := K) v)
      (localSol hc (basePlace (K := K) v)) / c (orbitRep (K := K) v)

theorem localPiece_apply {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (v : Place L) :
    localPiece hc v v = (((orbitRep (K := K) v) • onePlace (basePlace (K := K) v)
      (localSol hc (basePlace (K := K) v))) / c (orbitRep (K := K) v)) v := rfl

/-- The places at which the splitting idèle can fail to be a local unit form a finite set. -/
theorem badSet_y_finite (c : (L ≃ₐ[K] L) → Idele L) :
    ({v : Place L | basePlace (K := K) v ∈ badSet (K := K) c} ∪
      {v : Place L | c (orbitRep (K := K) v) v ∉ Place.localUnits L v}).Finite := by
  have h1 : {v : Place L | basePlace (K := K) v ∈ badSet (K := K) c} ⊆
      ⋃ b ∈ badSet (K := K) c, MulAction.orbit (L ≃ₐ[K] L) b := by
    intro v hv
    refine Set.mem_iUnion.mpr ⟨basePlace (K := K) v, Set.mem_iUnion.mpr ⟨hv, ?_⟩⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (basePlace_rel (K := K) v))
    exact MulAction.mem_orbit_iff.mpr ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  have hfin1 : (⋃ b ∈ badSet (K := K) c, MulAction.orbit (L ≃ₐ[K] L) b).Finite :=
    Set.Finite.biUnion (badSet_finite (K := K) c) (fun b _ => orbit_finite (K := K) b)
  have h2 : {v : Place L | c (orbitRep (K := K) v) v ∉ Place.localUnits L v} ⊆
      ⋃ g : L ≃ₐ[K] L, {v : Place L | c g v ∉ Place.localUnits L v} := by
    intro v hv
    exact Set.mem_iUnion.mpr ⟨orbitRep (K := K) v, hv⟩
  have hfin2 : (⋃ g : L ≃ₐ[K] L, {v : Place L | c g v ∉ Place.localUnits L v}).Finite := by
    rw [← Set.biUnion_univ]
    exact Set.Finite.biUnion Set.finite_univ (fun g _ => by
      have hg : ∀ᶠ v in Filter.cofinite, c g v ∈ Place.localUnits L v := (c g).2
      rw [Filter.eventually_cofinite] at hg
      exact hg)
  exact (hfin1.subset h1).union (hfin2.subset h2)

/-- The components of the splitting idèle are local units at all but finitely many places. -/
theorem eventually_localPiece_mem {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) :
    ∀ᶠ v in Filter.cofinite, localPiece hc v v ∈ Place.localUnits L v := by
  rw [Filter.eventually_cofinite]
  refine (badSet_y_finite c).subset ?_
  intro v hv
  by_contra hnot
  have hb : basePlace (K := K) v ∉ badSet (K := K) c := fun h => hnot (Or.inl h)
  have hc' : c (orbitRep (K := K) v) v ∈ Place.localUnits L v := by
    by_contra h
    exact hnot (Or.inr h)
  exact hv (by
    rw [localPiece_apply, div_apply_idele]
    exact Subgroup.div_mem _ (smul_onePlace_mem_localUnits (K := K)
      (g := orbitRep (K := K) v)
      (localSol_mem_localUnits hc (basePlace (K := K) v) hb) v) hc')

/-- **The splitting idèle** of a multiplicative `1`-cocycle. -/
noncomputable def coboundary {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) : Idele L :=
  ⟨fun v => localPiece hc v v, eventually_localPiece_mem hc⟩

theorem coboundary_apply {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (v : Place L) :
    coboundary hc v = localPiece hc v v := rfl

/-! ## The cocycle identity for the splitting idèle -/

theorem arith {G : Type*} [CommGroup G] (X Y cg cγ c₂ : G) (h : Y / c₂ = X / cγ) :
    X / (cγ / cg) = cg * (Y / c₂) := by
  rw [h, div_div_eq_mul_div, ← mul_div_assoc cg X cγ, mul_comm X cg]

/-- The local contributions at a place computed with two different coset representatives agree. -/
theorem component_at {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (g : L ≃ₐ[K] L) (w : Place L) :
    ((orbitRep (K := K) (g • w)) • onePlace (basePlace (K := K) w)
        (localSol hc (basePlace (K := K) w))) (g • w)
      / (c (orbitRep (K := K) (g • w))) (g • w)
    = ((g * orbitRep (K := K) w) • onePlace (basePlace (K := K) w)
        (localSol hc (basePlace (K := K) w))) (g • w)
      / (c (g * orbitRep (K := K) w)) (g • w) := by
  have hγ : (g * orbitRep (K := K) w) • basePlace (K := K) w = g • w := by
    rw [mul_smul, orbitRep_spec]
  have h₂ : orbitRep (K := K) (g • w) • basePlace (K := K) w = g • w := by
    rw [← basePlace_smul (K := K) g w]
    exact orbitRep_spec (g • w)
  have hσ : ((g * orbitRep (K := K) w)⁻¹ * orbitRep (K := K) (g • w))
      • basePlace (K := K) w = basePlace (K := K) w := by
    rw [mul_smul, h₂, ← hγ, inv_smul_smul]
  let σ : MulAction.stabilizer (L ≃ₐ[K] L) (basePlace (K := K) w) :=
    ⟨(g * orbitRep (K := K) w)⁻¹ * orbitRep (K := K) (g • w), hσ⟩
  have hmul : (g * orbitRep (K := K) w) * σ.1 = orbitRep (K := K) (g • w) := by
    show (g * orbitRep (K := K) w)
      * ((g * orbitRep (K := K) w)⁻¹ * orbitRep (K := K) (g • w)) =
        orbitRep (K := K) (g • w)
    group
  have h := component_eq_of_stabilizer (w₀ := basePlace (K := K) w)
    (u := localSol hc (basePlace (K := K) w)) (V := g • w) hc
    (localSol_spec hc (basePlace (K := K) w)) (g * orbitRep (K := K) w) σ hγ
  rw [hmul] at h
  rwa [div_apply_idele, div_apply_idele] at h

/-- **The splitting idèle is a coboundary**: `g • y = c g * y` componentwise. -/
theorem actVal_coboundary_eq {c : (L ≃ₐ[K] L) → Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) (g : L ≃ₐ[K] L) (w : Place L) :
    actVal g w (coboundary hc w) = c g (g • w) * coboundary hc (g • w) := by
  have hstep : actVal g w (coboundary hc w) = (g • localPiece hc w) (g • w) := by
    rw [coboundary_apply]
    exact (smul_apply_smul_place g w (localPiece hc w)).symm
  have hg1 : g • localPiece hc w = ((g * orbitRep (K := K) w) • onePlace (basePlace (K := K) w)
      (localSol hc (basePlace (K := K) w))) / (g • c (orbitRep (K := K) w)) := by
    show g • (((orbitRep (K := K) w) • onePlace (basePlace (K := K) w)
        (localSol hc (basePlace (K := K) w))) / c (orbitRep (K := K) w)) = _
    rw [smul_div_idele, smul_smul]
  have hden : (g • c (orbitRep (K := K) w)) (g • w)
      = (c (g * orbitRep (K := K) w)) (g • w) / (c g) (g • w) := by
    have h1 : c (g * orbitRep (K := K) w) (g • w)
        = (g • c (orbitRep (K := K) w)) (g • w) * (c g) (g • w) := by
      rw [hc g (orbitRep (K := K) w), Idele.mul_apply]
    rw [h1, div_eq_mul_inv, mul_assoc, mul_inv_cancel, mul_one]
  have hy : coboundary hc (g • w) = ((orbitRep (K := K) (g • w)) • onePlace (basePlace (K := K) w)
      (localSol hc (basePlace (K := K) w)) / c (orbitRep (K := K) (g • w))) (g • w) := by
    rw [coboundary_apply]
    show (((orbitRep (K := K) (g • w)) • onePlace (basePlace (K := K) (g • w))
        (localSol hc (basePlace (K := K) (g • w)))) / c (orbitRep (K := K) (g • w))) (g • w) = _
    rw [basePlace_smul]
  rw [hstep, hg1, hy, div_apply_idele, div_apply_idele, hden]
  rw [component_at hc g w]
  rw [div_div_eq_mul_div, ← mul_div_assoc, mul_comm]

end Aux

open NK.GlobalCFT in
/-- **Hilbert 90 for the idèles**: every multiplicative `1`-cocycle of `Gal(L/K)` with values in
the idèle group `𝕀_L` is a coboundary. -/
theorem exists_idele_coboundary_of_isMulCocycle {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {c : (L ≃ₐ[K] L) → NK.GlobalCFT.Idele L}
    (hc : ∀ g h : L ≃ₐ[K] L, c (g * h) = g • c h * c g) :
    ∃ y : NK.GlobalCFT.Idele L, ∀ g : L ≃ₐ[K] L, g • y / y = c g := by
  refine ⟨coboundary hc, fun g => ?_⟩
  have hmain : g • coboundary hc = c g * coboundary hc := by
    refine Idele.ext fun v => ?_
    rw [Idele.mul_apply]
    have hv : g • (g⁻¹ • v) = v := smul_inv_smul g v
    have hkey := actVal_coboundary_eq hc g (g⁻¹ • v)
    calc (g • coboundary hc) v
        = hv ▸ ((g • coboundary hc) (g • (g⁻¹ • v))) :=
          (units_transport hv (g • coboundary hc)).symm
      _ = hv ▸ actVal g (g⁻¹ • v) (coboundary hc (g⁻¹ • v)) :=
          congrArg (castFun hv) (smul_apply_smul_place g (g⁻¹ • v) (coboundary hc))
      _ = hv ▸ (c g (g • (g⁻¹ • v)) * coboundary hc (g • (g⁻¹ • v))) :=
          congrArg (castFun hv) hkey
      _ = (hv ▸ c g (g • (g⁻¹ • v))) * (hv ▸ coboundary hc (g • (g⁻¹ • v))) :=
          cast_mul hv _ _
      _ = c g v * coboundary hc v := by
          rw [units_transport hv (c g), units_transport hv (coboundary hc)]
  rw [hmain, div_eq_mul_inv, mul_assoc, mul_inv_cancel, mul_one]

end NK.HassePrinciple

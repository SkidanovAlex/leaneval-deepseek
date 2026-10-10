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
import Submission.NK.HeckeL.Nonvanishing.artinLSeries_value_ne_zero
import Submission.NK.HeckeL.Series.artinPrimeSum_sub_artinLogEulerProduct_isBigO
import Submission.NK.HeckeL.Series.exp_artinLogEulerProduct
import Submission.NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct
import Submission.NK.HeckeL.heckeEulerProduct_eq_artinLSeries
import Submission.NK.HeckeL.primeSum_eq_artinPrimeSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain Filter Asymptotics
open scoped BigOperators Classical nonZeroDivisors Topology

open NK.GlobalCFT (Idele IdeleClassGroup)

noncomputable section

namespace NK.HeckeL.Consequences

/-!
# Consequences of the Hecke/Artin dictionary: boundedness of the character-twisted prime sum

This file proves `primeSum_isBigO`: for a non-trivial character `χ` of the ray class group, the
Hecke prime sum `∑_{𝔭 ∉ S} χ(𝔭) N𝔭^{-s}` stays bounded as `s → 1⁺`.

The proof transfers the Hecke regularity hypothesis to the Galois side along Artin reciprocity
(`artinLSeries_eq_heckeLSeries`), and then applies the Artin-side argument: `artinLogEulerProduct`
is a continuous branch of the logarithm of the Artin `L`-series, whose limit at `1⁺` is non-zero by
the non-vanishing input `NK.HeckeL.Nonvanishing.artinLSeries_value_ne_zero`; hence
`artinLogEulerProduct` is bounded, and it differs from the Artin prime sum by an `O(1)` term.

The analytic continuity of `artinLogEulerProduct` and the "continuous branch of the logarithm"
lemma are reproduced here so that this module does not import
`NK.HeckeL.Series.continuousOn_artinLogEulerProduct`; the latter and
`NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct` declare a common auxiliary lemma under the
same name, so no module may import both.
-/

/-! ## Continuity of the logarithmic Euler product -/

/-! ## Preparatory estimates -/

/-- A nonzero prime ideal of the ring of integers of a number field has absolute norm at least
`2`. -/
lemma absNorm_primeIdeal_ge_two {K : Type*} [Field K] [NumberField K]
    (𝔭 : NK.HeckeL.PrimeIdeal K) : 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := fun h =>
    𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := fun h =>
    𝔭.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/-- The modulus of a character value times a prime power: `‖χ(𝔭) N𝔭^{-s}‖ ≤ N𝔭^{-c}` for
`1 < c ≤ s`, `N𝔭 ≥ 2` and `‖χ(𝔭)‖ ≤ 1`. -/
lemma norm_mul_rpow_le {n : ℝ} (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {c s : ℝ}
    (hc : 1 < c) (hcs : c ≤ s) : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ ≤ n ^ (-c) := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnorm : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ = ‖a‖ * n ^ (-s) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hn0 _)]
  rw [hnorm]
  calc ‖a‖ * n ^ (-s) ≤ 1 * n ^ (-s) := by gcongr
    _ = n ^ (-s) := one_mul _
    _ ≤ n ^ (-c) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

/-- The same bound, strict, for `s > c > 1`. -/
lemma norm_mul_rpow_lt_half {n : ℝ} (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {c s : ℝ}
    (hc : 1 < c) (hcs : c < s) : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ < 1 / 2 := by
  refine lt_of_le_of_lt (norm_mul_rpow_le hn a ha hc hcs.le) ?_
  have h1 : n ^ (-c) ≤ (2 : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hn (by linarith)
  have h2 : (2 : ℝ) ^ (-c) < 1 / 2 := by
    have h3 := (Real.rpow_lt_rpow_left_iff (x := (2 : ℝ)) (by norm_num)).mpr
      (show (-c : ℝ) < (-1 : ℝ) by linarith)
    rw [Real.rpow_neg_one] at h3
    have h4 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith
  linarith

/-- The logarithmic Euler factor at a single prime is bounded by `(3/2) * N𝔭^{-c}` on
`(c, ∞)`, for `c > 1`. -/
lemma norm_neg_log_one_sub_le {n : ℝ} (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {c s : ℝ}
    (hc : 1 < c) (hcs : c < s) :
    ‖-Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖ ≤ (3 / 2) * n ^ (-c) := by
  have hnorm : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ ≤ 1 / 2 :=
    (norm_mul_rpow_lt_half hn a ha hc hcs).le
  have hlog : ‖Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖ ≤
      (3 / 2) * ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ := by
    have h1 := Complex.norm_log_one_add_half_le_self
      (z := -(a * ((n ^ (-s) : ℝ) : ℂ))) (by rw [norm_neg]; exact hnorm)
    rwa [← sub_eq_add_neg, norm_neg] at h1
  calc ‖-Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖
      = ‖Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖ := norm_neg _
    _ ≤ (3 / 2) * ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ := hlog
    _ ≤ (3 / 2) * n ^ (-c) := by
        gcongr
        exact norm_mul_rpow_le hn a ha hc hcs.le

/-- Continuity of a single logarithmic Euler factor on `(s₀, ∞)` for `s₀ > 1`. -/
lemma continuousOn_logEulerTerm (n : ℝ) (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {s₀ : ℝ}
    (hs₀ : 1 < s₀) :
    ContinuousOn (fun s : ℝ => -Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))) (Set.Ioi s₀) := by
  have hnpos : n ≠ 0 := by linarith
  have hcont : ContinuousOn (fun s : ℝ => 1 - a * ((n ^ (-s) : ℝ) : ℂ)) (Set.Ioi s₀) :=
    (continuous_const.sub (continuous_const.mul <|
      Complex.continuous_ofReal.comp <|
        (Real.continuous_const_rpow hnpos).comp continuous_neg)).continuousOn
  refine (hcont.clog fun s hs => ?_).neg
  have hlt : ‖-(a * ((n ^ (-s) : ℝ) : ℂ))‖ < 1 := by
    rw [norm_neg]
    exact lt_of_lt_of_le (norm_mul_rpow_lt_half hn a ha hs₀ hs) (by norm_num)
  have := Complex.mem_slitPlane_of_norm_lt_one hlt
  simpa [sub_eq_add_neg] using this

/-! ## Continuity of the logarithmic Euler product -/

theorem continuousOn_artinLogEulerProduct {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ) :
    ContinuousOn (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s) (Set.Ioi 1) := by
  haveI : Fintype Gal(L/K) := AlgEquiv.fintype K L
  have hnorm_one : ∀ g : Gal(L/K), ‖(χ g : ℂ)‖ = 1 := fun g =>
    NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ g
  have key : ∀ c : ℝ, 1 < c →
      ContinuousOn (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s) (Set.Ioi c) := by
    intro c hc
    simp only [NK.HeckeL.artinLogEulerProduct]
    refine continuousOn_tsum
      (u := fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
        (3 / 2) * (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-c)) ?_ ?_ ?_
    · intro 𝔭
      refine continuousOn_logEulerTerm (Ideal.absNorm 𝔭.1.asIdeal : ℝ)
        (by exact_mod_cast absNorm_primeIdeal_ge_two 𝔭.1)
        (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ)
        (le_of_eq (hnorm_one (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1))) hc
    · have hsum : Summable (fun 𝔭 : NK.HeckeL.PrimeIdeal K =>
          (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-c)) :=
        Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hc
      exact (hsum.mul_left (3 / 2)).subtype (fun 𝔭 => 𝔭 ∉ S)
    · intro 𝔭 s hs
      exact norm_neg_log_one_sub_le (by exact_mod_cast absNorm_primeIdeal_ge_two 𝔭.1)
        (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ)
        (le_of_eq (hnorm_one (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1))) hc hs
  refine continuousOn_of_locally_continuousOn fun x hx => ?_
  obtain ⟨c, h1c, hcx⟩ := exists_between (show (1 : ℝ) < x from hx)
  exact ⟨Set.Ioi c, isOpen_Ioi, hcx, by
    rw [Set.Ioi_inter_Ioi, max_eq_right h1c.le]
    exact key c h1c⟩
/-! ## A continuous branch of the logarithm tending to a non-zero limit is bounded -/

/-- **A continuous branch of the logarithm of a function tending to a non-zero limit is bounded.**

If `f` is continuous on `(1, ∞)` and `exp ∘ f` tends to a non-zero limit `w` as `s → 1⁺`, then `f`
is `O(1)` near `1⁺`.

Indeed `exp (f s) / w → 1`, so on a small interval `(1, 1+ε)` the auxiliary function
`g s = log (exp (f s) / w) + log w` is a continuous branch of the logarithm of `exp ∘ f`, hence
`f - g` is continuous there with values in the discrete subgroup `2πiℤ`; being defined on a
connected set it is constant, so `f` differs from the bounded function `g` by a constant. -/
lemma isBigO_of_tendsto_exp_ne_zero {f : ℝ → ℂ} {w : ℂ}
    (hf : ContinuousOn f (Set.Ioi 1))
    (ht : Tendsto (fun s => Complex.exp (f s)) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 w))
    (hw : w ≠ 0) :
    f =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  have hL' : Tendsto (fun s : ℝ => Complex.exp (f s) / w)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 1) := by
    simpa [div_self hw] using ht.div_const w
  -- On a small interval to the right of `1` the quotient `exp (f s) / w` stays in the right
  -- half-plane, hence in the slit plane.
  have hU : {y : ℂ | (1 : ℝ) / 2 < y.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (by norm_num)
  have hev : ∀ᶠ s in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      (1 : ℝ) / 2 < (Complex.exp (f s) / w).re := hL'.eventually hU
  obtain ⟨e, he, hesub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set ε : ℝ := min e 1 / 2 with hεdef
  have hε : 0 < ε := by
    have : 0 < min e 1 := lt_min he one_pos
    linarith
  have hεe : ε < e := by
    have hle : ε ≤ e / 2 := by
      rw [hεdef]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith [lt_min he one_pos]
  have hε1 : ε < 1 := by
    have hle : ε ≤ 1 / 2 := by
      rw [hεdef]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith
  have hfε : ContinuousOn f (Set.Ioo (1 : ℝ) (1 + ε)) := hf.mono (fun s hs => hs.1)
  have hmemε : ∀ s ∈ Set.Ioo (1 : ℝ) (1 + ε),
      (1 : ℝ) / 2 < (Complex.exp (f s) / w).re := by
    intro s hs
    apply hesub
    refine ⟨?_, hs.1⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : (1 : ℝ) < s := hs.1
    have h2 : s < 1 + ε := hs.2
    rw [abs_of_pos (by linarith : (0 : ℝ) < s - 1)]
    linarith
  set g : ℝ → ℂ := fun s => Complex.log (Complex.exp (f s) / w) + Complex.log w with hgdef
  have hgcont : ContinuousOn g (Set.Ioo (1 : ℝ) (1 + ε)) := by
    have h1 : ContinuousOn (fun s : ℝ => Complex.exp (f s) / w) (Set.Ioo (1 : ℝ) (1 + ε)) :=
      (hfε.cexp).div_const w
    have h2 : ContinuousOn (fun s : ℝ => Complex.log (Complex.exp (f s) / w))
        (Set.Ioo (1 : ℝ) (1 + ε)) :=
      h1.clog (fun s hs => Complex.mem_slitPlane_iff.mpr
        (Or.inl (by linarith [hmemε s hs] : (0 : ℝ) < (Complex.exp (f s) / w).re)))
    simpa [hgdef] using h2.add_const (Complex.log w)
  have hexp : ∀ s ∈ Set.Ioo (1 : ℝ) (1 + ε), Complex.exp (f s) = Complex.exp (g s) := by
    intro s _hs
    have hz : Complex.exp (f s) / w ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) hw
    simp only [hgdef]
    rw [Complex.exp_add, Complex.exp_log hz, Complex.exp_log hw, div_mul_cancel₀ _ hw]
  have hgl : Tendsto g (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (Complex.log w)) := by
    have h1 : Tendsto (fun s : ℝ => Complex.log (Complex.exp (f s) / w))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (Complex.log 1)) :=
      hL'.clog (by simp [Complex.mem_slitPlane_iff])
    have := h1.add_const (Complex.log w)
    simpa [hgdef, Complex.log_one] using this
  have hgO : g =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    hgl.isBigO_one ℂ
  -- The connectedness argument: `f - g` is continuous and `2πiℤ`-valued on `(1, 1+ε)`.
  have hS : IsPreconnected (Set.Ioo (1 : ℝ) (1 + ε)) := isPreconnected_Ioo
  have hFcont : ContinuousOn (fun s : ℝ => f s - g s) (Set.Ioo (1 : ℝ) (1 + ε)) :=
    hfε.sub hgcont
  have hT : IsDiscrete
      (((AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I) : AddSubgroup ℂ)) : Set ℂ) := by
    rw [isDiscrete_iff_discreteTopology]
    exact NormedSpace.discreteTopology_zmultiples _
  have hmap : Set.MapsTo (fun s : ℝ => f s - g s) (Set.Ioo (1 : ℝ) (1 + ε))
      (((AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I) : AddSubgroup ℂ)) : Set ℂ) := by
    intro s hs
    have hexps : Complex.exp (f s - g s) = 1 := by
      rw [Complex.exp_sub, hexp s hs, div_self (Complex.exp_ne_zero (g s))]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexps
    change f s - g s ∈ AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I)
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul]
    exact hn.symm
  have hconst : ∀ x ∈ Set.Ioo (1 : ℝ) (1 + ε), ∀ y ∈ Set.Ioo (1 : ℝ) (1 + ε),
      f x - g x = f y - g y :=
    fun x hx y hy => hS.constant_of_mapsTo hT hFcont hmap hx hy
  have hmem : (1 + ε / 2) ∈ Set.Ioo (1 : ℝ) (1 + ε) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have hnb : Set.Ioo (1 : ℝ) (1 + ε) ∈ nhdsWithin (1 : ℝ) (Set.Ioi 1) := by
    rw [Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hε, ?_⟩
    intro s hs
    obtain ⟨hsb, hsi⟩ := hs
    have hs1 : (1 : ℝ) < s := hsi
    have h1 : |s - 1| < ε := by simpa [Real.dist_eq] using (Metric.mem_ball.mp hsb)
    rw [abs_of_pos (by linarith : (0 : ℝ) < s - 1)] at h1
    exact ⟨hs1, by linarith⟩
  have heq : (fun s : ℝ => f s) =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
      (fun s : ℝ => g s + (f (1 + ε / 2) - g (1 + ε / 2))) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (1 : ℝ) (1 + ε), hnb, ?_⟩
    intro s hs
    exact sub_eq_iff_eq_add'.mp (hconst s hs _ hmem)
  have hb : (fun s : ℝ => g s + (f (1 + ε / 2) - g (1 + ε / 2)))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    hgO.add (isBigO_const_one ℂ (f (1 + ε / 2) - g (1 + ε / 2)) _)
  exact hb.congr' heq.symm Filter.EventuallyEq.rfl
theorem artinPrimeSum_isBigO' {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (h : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ)
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  -- the value of the `L`-series at `1` is non-zero (non-vanishing input)
  have hv : (h χ hχ).value ≠ 0 := NK.HeckeL.Nonvanishing.artinLSeries_value_ne_zero S hcomm hS h χ hχ
  -- `artinLogEulerProduct` is a continuous branch of `log (artinLSeries ·)`, whence bounded.
  have hteq : (fun s : ℝ => Complex.exp (NK.HeckeL.artinLogEulerProduct K L S χ s))
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun s : ℝ => NK.HeckeL.artinLSeries K L S χ s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact NK.HeckeL.Series.exp_artinLogEulerProduct S χ hs
  have ht : Tendsto (fun s : ℝ => Complex.exp (NK.HeckeL.artinLogEulerProduct K L S χ s))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (h χ hχ).value) :=
    Filter.Tendsto.congr' hteq.symm (h χ hχ).tendsto
  have hfO : (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    isBigO_of_tendsto_exp_ne_zero
      (continuousOn_artinLogEulerProduct S χ) ht hv
  -- `artinPrimeSum` differs from `artinLogEulerProduct` by an `O(1)` term.
  have hsub : (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s -
        NK.HeckeL.artinLogEulerProduct K L S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    NK.HeckeL.Series.artinPrimeSum_sub_artinLogEulerProduct_isBigO S χ
  have hdecomp : (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s)
      = (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s -
            NK.HeckeL.artinLogEulerProduct K L S χ s)
        + (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s) := by
    ext s
    simp only [Pi.add_apply, sub_add_cancel]
  rw [hdecomp]
  exact hsub.add hfO
/-! ## Transfer of the regularity input to the Galois side -/

/-- On the half-plane `s > 1` the Hecke `L`-series of a ray class character equals the Artin
`L`-series of the corresponding Galois character: the Dirichlet series is the Euler product
(`NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct`) and the Euler factors agree under Artin
reciprocity (`NK.HeckeL.heckeEulerProduct_eq_artinLSeries`). -/
theorem heckeLSeries_eq_artinLSeries {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (χ : NK.HeckeL.RayChar K U) {s : ℝ} (hs : 1 < s) :
    NK.HeckeL.heckeLSeries K U S χ s =
      NK.HeckeL.artinLSeries K L S (NK.HeckeL.rayCharEquivGalois h e χ) s := by
  rw [NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct U S χ hs,
    NK.HeckeL.heckeEulerProduct_eq_artinLSeries h e S hFrob χ s]

/-- Transfer of the named regularity input from the Hecke side to the Artin side along the
Artin-reciprocity dictionary of characters: a non-trivial Galois character `ψ` is the image of a
non-trivial ray class character `χ`, and `L`-series regularity is preserved. -/
def artinLRegular_of_heckeLRegular {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (hH : ∀ χ : NK.HeckeL.RayChar K U, χ ≠ 1 → NK.HeckeL.HeckeLRegularAtOne K U S χ) :
    ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ := by
  intro ψ hψ
  have hχ : (NK.HeckeL.rayCharEquivGalois h e).symm ψ ≠ 1 := by
    intro h1
    apply hψ
    have h2 := congrArg (NK.HeckeL.rayCharEquivGalois h e) h1
    simpa using h2
  refine ⟨(hH _ hχ).value, ?_⟩
  refine (hH _ hχ).tendsto.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hmem : (NK.HeckeL.rayCharEquivGalois h e) ((NK.HeckeL.rayCharEquivGalois h e).symm ψ) = ψ :=
    MulEquiv.apply_symm_apply _ _
  rw [heckeLSeries_eq_artinLSeries h e S hFrob ((NK.HeckeL.rayCharEquivGalois h e).symm ψ) hs, hmem]


/-! ## The main theorem -/

theorem primeSum_isBigO {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (hH : ∀ χ : NK.HeckeL.RayChar K U, χ ≠ 1 → NK.HeckeL.HeckeLRegularAtOne K U S χ)
    (χ : NK.HeckeL.RayChar K U) (hχ : χ ≠ 1) :
    (fun s : ℝ => NK.HeckeL.primeSum K U S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  have hArtin : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ :=
    artinLRegular_of_heckeLRegular h e S hFrob hH
  have hχ' : NK.HeckeL.rayCharEquivGalois h e χ ≠ 1 :=
    fun h1 => hχ ((NK.HeckeL.rayCharEquivGalois_eq_one_iff h e).mp h1)
  have hb := artinPrimeSum_isBigO' (K := K) (L := L) S hcomm hS hArtin
    (NK.HeckeL.rayCharEquivGalois h e χ) hχ'
  have heq : (fun s : ℝ => NK.HeckeL.primeSum K U S χ s)
      = fun s : ℝ =>
          NK.HeckeL.artinPrimeSum K L S (NK.HeckeL.rayCharEquivGalois h e χ) s := by
    funext s
    exact NK.HeckeL.primeSum_eq_artinPrimeSum h e S hFrob χ s
  rw [heq]
  exact hb

end NK.HeckeL.Consequences

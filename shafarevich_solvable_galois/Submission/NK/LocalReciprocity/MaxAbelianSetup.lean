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
import Submission.NK.LocalReciprocity.commutator_gal_maxAbelianSubext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Levels of the maximal abelian subextension

For a Galois extension `F' / F` with maximal abelian subextension
`A = maxAbelianSubext F F' = fixedField (commutator Gal(F'/F))`, this file provides the
bookkeeping that lets us view a finite Galois level `L ≤ A` of the *sub*extension as a level of
the *ambient* extension `F'`:

* `levelMap L` is the image of `L` in `F'` under the inclusion `A → F'`;
* `levelEquiv L : L ≃ₐ[F] levelMap L` is the corresponding isomorphism;
* `levelMap_le L : levelMap L ≤ A`;
* the finiteness / normality / Galois instances transport along `levelEquiv`;
* `normGroup_levelMap : normGroup F L = normGroup F (levelMap L)`.

These are the tools needed to feed a level of `F^{ab}/F` to the reciprocity datum
`LocalReciprocityDatum F F'`, whose level isomorphisms are only available for levels of `F'/F`.
-/

universe u v

namespace NK.LocalReciprocity

open scoped Classical commutatorElement
open CategoryTheory

noncomputable section

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']

section LevelMap

/-- **The image of a level of `F^{ab}` inside `F'`.**  For `L : IntermediateField F (maxAbelianSubext F F')`
this is the subfield of `F'` generated by the elements of `L` (the inclusion `A ↪ F'` restricted
to `L`). -/
def levelMap (L : IntermediateField F (maxAbelianSubext F F')) : IntermediateField F F' :=
  L.map (IntermediateField.val (maxAbelianSubext F F'))

@[simp]
theorem levelMap_toSubalgebra (L : IntermediateField F (maxAbelianSubext F F')) :
    (levelMap L).toSubalgebra = L.toSubalgebra.map (IntermediateField.val (maxAbelianSubext F F')) :=
  rfl

/-- The inclusion `L → F'` of a level of `F^{ab}` into the ambient field, as an `F`-algebra map. -/
def levelIncl (L : IntermediateField F (maxAbelianSubext F F')) : ↥L →ₐ[F] F' :=
  (IntermediateField.val (maxAbelianSubext F F')).comp (IntermediateField.val L)

@[simp]
theorem levelIncl_apply (L : IntermediateField F (maxAbelianSubext F F')) (x : ↥L) :
    levelIncl L x = (x : F') := rfl

theorem levelIncl_eq_coe (L : IntermediateField F (maxAbelianSubext F F')) (x : ↥L) :
    levelIncl L x = (maxAbelianSubext F F').val (x : ↥(maxAbelianSubext F F')) := rfl

theorem mem_levelMap {L : IntermediateField F (maxAbelianSubext F F')} {x : F'} :
    x ∈ levelMap L ↔ ∃ y : ↥L, levelIncl L y = x := by
  rw [levelMap, IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y.1, y.2, hy⟩

theorem levelMap_mono {L₁ L₂ : IntermediateField F (maxAbelianSubext F F')} (h : L₁ ≤ L₂) :
    levelMap L₁ ≤ levelMap L₂ :=
  IntermediateField.map_mono _ h

theorem levelMap_le (L : IntermediateField F (maxAbelianSubext F F')) :
    levelMap L ≤ maxAbelianSubext F F' := by
  rw [levelMap, IntermediateField.map_le_iff_le_comap]
  refine fun x hx => ?_
  show (maxAbelianSubext F F').val x ∈ maxAbelianSubext F F'
  simpa using hx

/-- **The canonical isomorphism `L ≃ₐ[F] levelMap L`**, given by the inclusion of `L` into `F'`. -/
def levelEquiv (L : IntermediateField F (maxAbelianSubext F F')) : L ≃ₐ[F] levelMap L :=
  Subalgebra.equivMapOfInjective L.toSubalgebra (IntermediateField.val (maxAbelianSubext F F'))
    (IntermediateField.val (maxAbelianSubext F F')).injective

theorem levelIncl_levelEquiv (L : IntermediateField F (maxAbelianSubext F F')) (x : ↥L) :
    (levelEquiv L x : F') = levelIncl L x :=
  Subalgebra.coe_equivMapOfInjective_apply _ _ _ _

instance instFiniteDimensionalLevelMap (L : IntermediateField F (maxAbelianSubext F F'))
    [FiniteDimensional F L] : FiniteDimensional F (levelMap L) :=
  FiniteDimensional.of_surjective (levelEquiv L).toLinearMap (by simpa using (levelEquiv L).surjective)

instance instNormalLevelMap (L : IntermediateField F (maxAbelianSubext F F')) [Normal F L] :
    Normal F (levelMap L) :=
  Normal.of_algEquiv (levelEquiv L)

instance instIsGaloisLevelMap (L : IntermediateField F (maxAbelianSubext F F')) [IsGalois F L] :
    IsGalois F (levelMap L) :=
  IsGalois.of_algEquiv (levelEquiv L)

/-- **The norm group is unchanged** by viewing a level of `F^{ab}` inside `F'`. -/
theorem normGroup_levelMap (L : IntermediateField F (maxAbelianSubext F F')) :
    normGroup F ↥L = normGroup F ↥(levelMap L) :=
  normGroup_eq_of_algEquiv (levelEquiv L)

end LevelMap

section Galois

variable [IsGalois F F']

/-- **`F^{ab}` is Galois over `F`**: it is the fixed field of the (normal) commutator subgroup. -/
instance instIsGaloisMaxAbelianSubext : IsGalois F (maxAbelianSubext F F') :=
  IsGalois.of_fixedField_normal_subgroup (commutator (F' ≃ₐ[F] F'))

/-- **`Gal(F^{ab}/F)` is abelian**: it is the quotient of `Gal(F'/F)` by its commutator subgroup. -/
theorem commutative_gal_maxAbelianSubext :
    ∀ σ τ : (maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F'), σ * τ = τ * σ := by
  have h := commutator_gal_maxAbelianSubext (F := F) (F' := F')
  rw [commutator_eq_bot_iff] at h
  exact isMulCommutative_iff.mp h

/-- Every finite Galois level of `F^{ab}` is an abelian extension of `F`, so it can be fed to the
reciprocity datum (whose level isomorphisms are stated for abelian levels). -/
theorem commutative_levelMap (L : IntermediateField F (maxAbelianSubext F F')) [Normal F L] :
    ∀ σ τ : ↥(levelMap L) ≃ₐ[F] ↥(levelMap L), σ * τ = τ * σ := by
  -- the commutator subgroup of `Gal(F'/F)` fixes `maxAbelianSubext F F'`, hence also `levelMap L`
  have hfix : commutator (F' ≃ₐ[F] F') ≤ (levelMap L).fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).mp (levelMap_le L)
  intro σ τ
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := ↥(levelMap L)) (E := F') σ
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := ↥(levelMap L)) (E := F') τ
  have hmem : ⁅σ, τ⁆ ∈ (levelMap L).fixingSubgroup :=
    hfix (Subgroup.commutator_mem_commutator (Subgroup.mem_top σ) (Subgroup.mem_top τ))
  have hker : (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) ⁅σ, τ⁆ = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hmem
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at hker
  calc (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) σ *
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) τ
      = (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) σ *
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) τ *
        ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) σ)⁻¹ *
        ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) τ)⁻¹ *
        ((AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) τ *
         (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) σ) := by group
    _ = (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) τ *
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥(levelMap L)) σ := by
          rw [hker, one_mul]

end Galois

section Reciprocity

variable [IsGalois F F'] (D : LocalReciprocityDatum F F')

/-- **The norm group of a level of `F^{ab}` as a finite-index normal subgroup of `Fˣ`.**

It is finite index because it is the kernel of the Artin map to the finite group
`Gal(levelMap L/F)` (this is `D.isLevelIso`), and normal because it is a kernel. -/
abbrev normSub (L : FiniteGaloisIntermediateField F (maxAbelianSubext F F')) :
    FiniteIndexNormalSubgroup Fˣ where
  toSubgroup := normGroup F ↥(levelMap (L : IntermediateField F (maxAbelianSubext F F')))
  isNormal' := by
    rw [← (D.isLevelIso (levelMap (L : IntermediateField F (maxAbelianSubext F F')))
      (commutative_levelMap _)).2]
    infer_instance
  isFiniteIndex' := by
    rw [← (D.isLevelIso (levelMap (L : IntermediateField F (maxAbelianSubext F F')))
      (commutative_levelMap _)).2]
    exact Subgroup.finiteIndex_ker _

theorem levelIncl_symm_levelEquiv (L : IntermediateField F (maxAbelianSubext F F'))
    (y : ↥(levelMap L)) : levelIncl L ((levelEquiv L).symm y) = (y : F') := by
  rw [← levelIncl_levelEquiv, AlgEquiv.apply_symm_apply]

/-- The reciprocity isomorphism at a level of `F^{ab}`**, expressed in terms of the level itself
(not of its image in `F'`):

  `Fˣ ⧸ N(L) ≃* Gal(L/F)`.

It is the level isomorphism of the datum at `levelMap L`, transported along the canonical
isomorphism `Gal(L/F) ≃* Gal(levelMap L/F)`. -/
def levelMulEquiv (L : FiniteGaloisIntermediateField F (maxAbelianSubext F F')) :
    Fˣ ⧸ (normSub D L).toSubgroup ≃* (↥L ≃ₐ[F] ↥L) :=
  (D.artinLevelMulEquiv (levelMap (L : IntermediateField F (maxAbelianSubext F F')))
      (commutative_levelMap _)).trans
    (AlgEquiv.autCongr (levelEquiv (L : IntermediateField F (maxAbelianSubext F F')))).symm

/-- **The restriction map between two levels**, in the exact form used by
`InfiniteGalois.asProfiniteGaloisGroupFunctor`:  an automorphism of the larger level restricts to
the smaller level. -/
def levelRestrict {L₁ L₂ : (FiniteGaloisIntermediateField F (maxAbelianSubext F F'))ᵒᵖ}
    (π : L₁ ⟶ L₂) :
    (↥(L₁.unop).toIntermediateField ≃ₐ[F] ↥(L₁.unop).toIntermediateField) →*
      (↥(L₂.unop).toIntermediateField ≃ₐ[F] ↥(L₂.unop).toIntermediateField) := by
  letI : Algebra ↥(L₂.unop).toIntermediateField ↥(L₁.unop).toIntermediateField :=
    RingHom.toAlgebra (Subsemiring.inclusion (leOfHom π.unop))
  haveI : IsScalarTower F ↥(L₂.unop).toIntermediateField ↥(L₁.unop).toIntermediateField :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact AlgEquiv.restrictNormalHom (K₁ := ↥(L₁.unop).toIntermediateField)
    ↥(L₂.unop).toIntermediateField

/-- `levelRestrict` is the map induced by the functor `asProfiniteGaloisGroupFunctor`. -/
theorem levelRestrict_eq_finGaloisGroupFunctor_map
    {L₁ L₂ : (FiniteGaloisIntermediateField F (maxAbelianSubext F F'))ᵒᵖ} (π : L₁ ⟶ L₂)
    (x : ↥(L₁.unop).toIntermediateField ≃ₐ[F] ↥(L₁.unop).toIntermediateField) :
    (ProfiniteGrp.Hom.hom ((CategoryTheory.forget₂ FiniteGrp ProfiniteGrp).map
        ((finGaloisGroupFunctor F (maxAbelianSubext F F')).map π))) x = levelRestrict π x := rfl

/-- Unfolding lemma for `levelMulEquiv`: it is the level isomorphism of the datum at
`levelMap L`, transported back along `AlgEquiv.autCongr` of the canonical isomorphism
`L ≃ₐ[F] levelMap L`. -/
theorem levelMulEquiv_apply (L : FiniteGaloisIntermediateField F (maxAbelianSubext F F'))
    (y : Fˣ ⧸ (normSub D L).toSubgroup) :
    levelMulEquiv D L y =
      (AlgEquiv.autCongr (levelEquiv (L : IntermediateField F (maxAbelianSubext F F')))).symm
        ((D.artinLevelMulEquiv (levelMap (L : IntermediateField F (maxAbelianSubext F F')))
          (commutative_levelMap _)) y) := rfl

/-- The values of the restriction map on elements: restricting an automorphism of the larger level
to the smaller level and evaluating agrees with evaluating the automorphism on the same element. -/
theorem levelIncl_levelRestrict {L₁ L₂ : (FiniteGaloisIntermediateField F (maxAbelianSubext F F'))ᵒᵖ}
    (π : L₁ ⟶ L₂)
    (σ : ↥(L₁.unop).toIntermediateField ≃ₐ[F] ↥(L₁.unop).toIntermediateField)
    (x : ↥(L₂.unop).toIntermediateField) :
    levelIncl (L₂.unop : IntermediateField F (maxAbelianSubext F F')) ((levelRestrict π σ) x) =
      levelIncl (L₁.unop : IntermediateField F (maxAbelianSubext F F'))
        (σ ⟨x.1, (leOfHom π.unop) x.2⟩) := by
  letI : Algebra ↥(L₂.unop).toIntermediateField ↥(L₁.unop).toIntermediateField :=
    RingHom.toAlgebra (Subsemiring.inclusion (leOfHom π.unop))
  haveI : IsScalarTower F ↥(L₂.unop).toIntermediateField ↥(L₁.unop).toIntermediateField :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [levelRestrict, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, levelIncl_eq_coe,
    levelIncl_eq_coe]
  have h2 : (maxAbelianSubext F F').val
        (((σ.restrictNormal ↥(L₂.unop).toIntermediateField) x :
          ↥(L₂.unop).toIntermediateField) : ↥(maxAbelianSubext F F')) =
      (maxAbelianSubext F F').val
        (((algebraMap ↥(L₂.unop).toIntermediateField ↥(L₁.unop).toIntermediateField
          ((σ.restrictNormal ↥(L₂.unop).toIntermediateField) x)) :
            ↥(L₁.unop).toIntermediateField) : ↥(maxAbelianSubext F F')) := rfl
  rw [h2, AlgEquiv.restrictNormal_commutes]
  rfl

/-- **The value of the reciprocity isomorphism on a unit**:  the level isomorphism at `L` sends
the class of `a : Fˣ` to the automorphism which acts on `L ⊆ F^{ab} ⊆ F'` as `D.artin a` does. -/
theorem levelIncl_levelMulEquiv_mk (L : FiniteGaloisIntermediateField F (maxAbelianSubext F F'))
    (a : Fˣ) (x : ↥L) :
    levelIncl (L : IntermediateField F (maxAbelianSubext F F'))
        ((levelMulEquiv D L (QuotientGroup.mk a)) x) =
      D.artin a (levelIncl (L : IntermediateField F (maxAbelianSubext F F')) x) := by
  simp only [normSub]
  rw [levelMulEquiv_apply]
  simp only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_symm]
  rw [levelIncl_symm_levelEquiv]
  rw [D.artinLevelMulEquiv_mk]
  rw [AlgEquiv.restrictNormalHom_apply]
  rw [levelIncl_levelEquiv]

/-- **Compatibility of the level isomorphisms with restriction**:  the reciprocity isomorphism
at a level of `F^{ab}`, followed by the restriction of automorphisms to a smaller level, is the
reciprocity isomorphism of the smaller level (on the image of the class in the smaller quotient). -/
theorem levelMulEquiv_levelRestrict
    {L₁ L₂ : (FiniteGaloisIntermediateField F (maxAbelianSubext F F'))ᵒᵖ} (π : L₁ ⟶ L₂) (a : Fˣ) :
    levelRestrict π (levelMulEquiv D L₁.unop (QuotientGroup.mk a)) =
      levelMulEquiv D L₂.unop (QuotientGroup.mk a) := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rw [show (↑↑(((levelRestrict π) ((levelMulEquiv D L₁.unop) (QuotientGroup.mk a))) x) : F') =
      levelIncl (L₂.unop : IntermediateField F (maxAbelianSubext F F'))
        ((levelRestrict π) ((levelMulEquiv D L₁.unop) (QuotientGroup.mk a)) x) from rfl]
  rw [levelIncl_levelRestrict]
  rw [levelIncl_levelMulEquiv_mk]
  rw [show levelIncl (L₁.unop : IntermediateField F (maxAbelianSubext F F'))
        (⟨x.1, (leOfHom π.unop) x.2⟩ : ↥(L₁.unop).toIntermediateField) =
      levelIncl (L₂.unop : IntermediateField F (maxAbelianSubext F F')) x from rfl]
  rw [← levelIncl_levelMulEquiv_mk]
  rfl

/-- **Compatibility of the level isomorphisms with the map on finite quotients induced by the
completion diagram**:  for levels `L₂ ≤ L₁`, the reciprocity isomorphism at `L₁` followed by the
restriction to `L₂` is the reciprocity isomorphism at `L₂` after the quotient map
`Fˣ ⧸ N(L₁) → Fˣ ⧸ N(L₂)`. -/
theorem levelMulEquiv_diagram
    {L₁ L₂ : (FiniteGaloisIntermediateField F (maxAbelianSubext F F'))ᵒᵖ} (π : L₁ ⟶ L₂)
    (h : normSub D L₁.unop ≤ normSub D L₂.unop)
    (y : Fˣ ⧸ (normSub D L₁.unop).toSubgroup) :
    levelRestrict π (levelMulEquiv D L₁.unop y) =
      levelMulEquiv D L₂.unop
        ((ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Fˣ)).map (h.hom) y) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  have hd : ∀ z : Fˣ ⧸ (normSub D L₁.unop).toSubgroup,
      (ProfiniteGrp.Hom.hom ((ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Fˣ)).map h.hom)) z
        = QuotientGroup.map (normSub D L₁.unop).toSubgroup (normSub D L₂.unop).toSubgroup
            (MonoidHom.id Fˣ) h z := fun z => rfl
  rw [hd]
  have hh : (normSub D L₁.unop).toSubgroup ≤
      Subgroup.comap (MonoidHom.id Fˣ) (normSub D L₂.unop).toSubgroup := fun x hx => h hx
  rw [show QuotientGroup.map (normSub D L₁.unop).toSubgroup (normSub D L₂.unop).toSubgroup
        (MonoidHom.id Fˣ) h = QuotientGroup.map _ _ (MonoidHom.id Fˣ) hh from rfl]
  rw [QuotientGroup.map_mk]
  exact levelMulEquiv_levelRestrict D π a

end Reciprocity

end

end NK.LocalReciprocity

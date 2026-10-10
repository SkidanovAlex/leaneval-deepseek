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
import Submission.NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces
import Submission.NK.NUV2.HeckeAnalytic.Transfer
import Submission.NK.NUV2.RouteB.CongCount.CongRayAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ray-class/lattice dictionary for the congruence subgroup `U(𝔪)`: setup

For a number field `K`, a modulus `𝔪` with `𝔪.pos = ∅` and a nonzero integral ideal `𝔡` coprime to
the support of `𝔪`, we fix the objects and the elementary facts used in the proof of
`NK.NUV2.RouteB.CongCount.torsionOrder_mul_rayClassCnt_eq_sum`.

* `magIdeal 𝔪 𝔡` — the (nonzero) fractional ideal `𝔪.ideal · 𝔡⁻¹`;
* `count_magIdeal` — its `q`-adic `count`s: `𝔪.exps q - count q 𝔡` (so `𝔪.exps q` at the support
  primes, by coprimality);
* `mem_iff_count_le` — the characterisation of membership in a nonzero fractional ideal by the
  `count`s: `x ∈ M ↔ ∀ q, count q M ≤ -log (v_q x)`;
* `mem_magIdeal_iff_mem_ideal` — an *algebraic integer* lies in `𝔪.ideal · 𝔡⁻¹` iff it lies in
  `𝔪.ideal`;
* `isCongElem_iff_sub_mem_magIdeal` — the *dictionary*: for `β ∈ 𝔡⁻¹` and a unit `u`, the element
  `uβ` is `≡ 1 (mod 𝔪)` iff `β - u⁻¹` lies in the lattice `𝔪.ideal · 𝔡⁻¹`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

noncomputable section

namespace NK.NUV2.RouteB.CongCount

open NK.NUV2.RouteB
open NK.GlobalCFT.IdeleClassGroup (count_spanSingleton_eq)

variable {K : Type} [Field K] [NumberField K]

/-! ## The lattice fractional ideal `𝔪.ideal · 𝔡⁻¹` -/

/-- The inverse of a unit of `𝓞 K`, viewed as an element of `K`. -/
def unitInvK (u : (𝓞 K)ˣ) : K := (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)

@[simp]
theorem unitInvK_def (u : (𝓞 K)ˣ) : unitInvK u = (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) := rfl

/-- The lattice `𝔪.ideal · 𝔡⁻¹` of the modulus `𝔪` and the base ideal `𝔡`, as a fractional ideal
(nonzero). -/
noncomputable def magIdeal (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Modulus.fracIdeal 𝔪 𝔡

@[simp]
theorem coe_magIdeal (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K)
        * ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [magIdeal, Modulus.fracIdeal, Units.val_mul, Units.val_inv_eq_inv_val,
    FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0]
  rfl

/-- The base ideal is nonzero. -/
theorem baseIdeal_ne_zero (𝔡 : (Ideal (𝓞 K))⁰) : (𝔡 : Ideal (𝓞 K)) ≠ 0 :=
  mem_nonZeroDivisors_iff_ne_zero.mp 𝔡.2

theorem magIdeal_ne_zero (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
  Units.ne_zero _

/-! ## The `count`s of the modulus ideal and of the lattice -/

/-- The `q`-adic `count` of the integral ideal of the modulus is the exponent of the modulus. -/
theorem count_modulusIdeal (𝔪 : Modulus K) (q : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K q (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K) = (𝔪.exps q : ℤ) := by
  classical
  have hne : ∀ q' ∈ 𝔪.supportFinset,
      ((q'.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ (𝔪.exps q') ≠ 0 := by
    intro q' _
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr q'.ne_bot)
  rw [Modulus.ideal, NK.NUV2.RouteB.Sharp.coeIdeal_finset_prod]
  simp only [FractionalIdeal.coeIdeal_pow]
  rw [FractionalIdeal.count_prod K q 𝔪.supportFinset
    (fun q' => ((q'.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ (𝔪.exps q')) hne]
  have hkey : ∀ q' ∈ 𝔪.supportFinset,
      FractionalIdeal.count K q
        (((q'.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ (𝔪.exps q'))
      = if q' = q then (𝔪.exps q' : ℤ) else 0 := by
    intro q' _
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal]
    by_cases h : q' = q
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hkey,
    Finset.sum_ite_eq' 𝔪.supportFinset q fun q' => (𝔪.exps q' : ℤ)]
  by_cases hq : q ∈ 𝔪.supportFinset
  · rw [if_pos hq]
  · rw [if_neg hq, Modulus.exps_eq_zero_of_not_mem 𝔪 hq]
    simp

/-- A prime not dividing an integral ideal has `count` zero there. -/
theorem count_coe_eq_zero_of_not_dvd {𝔠 : Ideal (𝓞 K)} (h𝔠 : 𝔠 ≠ 0)
    {q : HeightOneSpectrum (𝓞 K)} (h : ¬ q.asIdeal ∣ 𝔠) :
    FractionalIdeal.count K q (𝔠 : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rw [FractionalIdeal.count_coe K q h𝔠, Ideal.count_associates_factors_eq h𝔠 q.isPrime q.ne_bot]
  have hz : Multiset.count q.asIdeal (UniqueFactorizationMonoid.normalizedFactors 𝔠) = 0 := by
    rw [Multiset.count_eq_zero]
    intro hmem
    exact h (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem)
  rw [hz]
  norm_num

/-- The `count`s of the lattice `𝔪.ideal · 𝔡⁻¹`. -/
theorem count_magIdeal (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (q : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K q
        ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = (𝔪.exps q : ℤ) - FractionalIdeal.count K q
          ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [coe_magIdeal,
    FractionalIdeal.count_mul K q (FractionalIdeal.coeIdeal_ne_zero.mpr 𝔪.ideal_ne_zero)
      (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr (baseIdeal_ne_zero 𝔡))),
    FractionalIdeal.count_inv, count_modulusIdeal]
  ring

/-- The `count`s of the lattice at the support primes of the modulus, where `𝔡` is a unit. -/
theorem count_magIdeal_of_exp_ne_zero (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    {q : HeightOneSpectrum (𝓞 K)} (hq : 𝔪.exps q ≠ 0) :
    FractionalIdeal.count K q
        ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = (𝔪.exps q : ℤ) := by
  have h0 : FractionalIdeal.count K q ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
    count_coe_eq_zero_of_not_dvd (baseIdeal_ne_zero 𝔡) (hcop q hq)
  rw [count_magIdeal]
  rw [h0]
  ring

/-! ## Membership in a nonzero fractional ideal, by `count`s -/

/-- **Membership in a nonzero fractional ideal, read off from the `count`s.**  For `x ≠ 0`,
`x` lies in `M` iff the `count` of `M` at every prime is at most the order of vanishing of `x`. -/
theorem mem_iff_count_le {M : FractionalIdeal (𝓞 K)⁰ K} (hM : M ≠ 0) {x : K} (hx : x ≠ 0) :
    x ∈ M ↔ ∀ q : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K q M ≤ -((q.valuation K) x).log := by
  constructor
  · intro hxM q
    have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ M :=
      FractionalIdeal.spanSingleton_le_iff_mem.mpr hxM
    have h1 : FractionalIdeal.count K q M ≤
        FractionalIdeal.count K q (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) :=
      FractionalIdeal.count_mono K q (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) hle
    rwa [count_spanSingleton_eq q hx] at h1
  · intro h
    have hS : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx
    have hN : M * (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)⁻¹ ≠ 0 :=
      mul_ne_zero hM (inv_ne_zero hS)
    have hcount : ∀ q : HeightOneSpectrum (𝓞 K),
        FractionalIdeal.count K q (M * (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)⁻¹) ≤ 0 := by
      intro q
      rw [FractionalIdeal.count_mul K q hM (inv_ne_zero hS), FractionalIdeal.count_inv,
        count_spanSingleton_eq q hx]
      have := h q
      linarith
    have hone : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤
        M * (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)⁻¹ :=
      NK.NUV2.RouteB.Sharp.one_le_of_count_nonpos hN hcount
    have hle := mul_le_mul_right hone (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
    have hsimp : FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
        (M * (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)⁻¹) = M := by
      rw [mul_comm M (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)⁻¹, ← mul_assoc,
        mul_inv_cancel₀ hS, one_mul]
    rw [mul_one, hsimp] at hle
    exact FractionalIdeal.spanSingleton_le_iff_mem.mp hle

/-! ## The order of vanishing of an algebraic integer -/

/-- The `q`-adic order of vanishing of an algebraic integer, via its `q`-adic integer
valuation. -/
theorem log_valuation_algebraMap (q : HeightOneSpectrum (𝓞 K)) (z : 𝓞 K) :
    ((q.valuation K) ((z : 𝓞 K) : K)).log = (q.intValuation z).log := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]

/-- An algebraic integer is integral at every finite place: its order of vanishing is
nonnegative. -/
theorem neg_log_valuation_nonneg (q : HeightOneSpectrum (𝓞 K)) (z : 𝓞 K) :
    0 ≤ -((q.valuation K) ((z : 𝓞 K) : K)).log := by
  rw [log_valuation_algebraMap]
  rcases eq_or_ne (q.intValuation z) 0 with hz | hz
  · rw [hz, WithZero.log_zero]
    simp
  · have h1 : (q.intValuation z).log ≤ 0 := by
      have h := IsDedekindDomain.HeightOneSpectrum.intValuation_le_one q z
      have h2 : (q.intValuation z).log ≤ (WithZero.exp (0 : ℤ)).log :=
        (WithZero.log_le_log hz (WithZero.exp_ne_zero (a := (0 : ℤ)))).mpr (by
          simpa using h)
      rwa [WithZero.log_exp] at h2
    linarith

/-- If `z ∈ q ^ n` then the order of vanishing of `z` at `q` is at least `n`. -/
theorem le_neg_log_valuation_of_mem_pow (q : HeightOneSpectrum (𝓞 K)) {z : 𝓞 K}
    (hz : z ≠ 0) (n : ℕ) (h : z ∈ q.asIdeal ^ n) :
    (n : ℤ) ≤ -((q.valuation K) ((z : 𝓞 K) : K)).log := by
  rw [log_valuation_algebraMap]
  have h1 := (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem q z n).mpr h
  have hz' : q.intValuation z ≠ 0 := q.intValuation_ne_zero z hz
  have h2 : (q.intValuation z).log ≤ (-(n : ℤ)) := by
    have h3 := (WithZero.log_le_log hz' (WithZero.exp_ne_zero (a := (-(n : ℤ))))).mpr h1
    rwa [WithZero.log_exp] at h3
  linarith

/-! ## The lattice, the modulus ideal and the integral ideals -/

/-- An integral ideal, as a fractional ideal, is at most one. -/
theorem coeIdeal_le_one (𝔠 : Ideal (𝓞 K)) :
    ((𝔠 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 := by
  have h : ((𝔠 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤
      ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr le_top
  simpa using h

/-- The integral ideal of the modulus, as a fractional ideal, is at most one. -/
theorem modulusIdeal_le_one (𝔪 : Modulus K) :
    (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 :=
  coeIdeal_le_one 𝔪.ideal

/-- The inverse of a nonzero integral ideal contains one. -/
theorem one_le_inv_coeIdeal (𝔠 : Ideal (𝓞 K)) (h𝔠 : 𝔠 ≠ 0) :
    (1 : FractionalIdeal (𝓞 K)⁰ K) ≤
      ((𝔠 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  refine NK.NUV2.RouteB.Sharp.one_le_of_count_nonpos
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔠)) (fun q => ?_)
  rw [FractionalIdeal.count_inv]
  exact neg_nonpos.mpr (FractionalIdeal.count_coe_nonneg K q 𝔠)

/-- The lattice is contained in `𝔡⁻¹`. -/
theorem magIdeal_le_inv_base (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      ≤ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coe_magIdeal]
  calc (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K)
        * ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
      ≤ 1 * ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
        mul_le_mul_left (modulusIdeal_le_one 𝔪) _
    _ = _ := one_mul _

/-- The lattice contains the modulus ideal. -/
theorem modulusIdeal_le_magIdeal (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K)
      ≤ ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
  have h := mul_le_mul_right (one_le_inv_coeIdeal (𝔡 : Ideal (𝓞 K)) (baseIdeal_ne_zero 𝔡))
    (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K)
  rw [mul_one] at h
  rw [coe_magIdeal]
  exact h

/-- The inverse of an integral ideal `𝔡`, as a fractional ideal. -/
def invBaseFrac (𝔡 : (Ideal (𝓞 K))⁰) : FractionalIdeal (𝓞 K)⁰ K :=
  ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹

@[simp]
theorem mem_invBaseFrac_iff {𝔡 : (Ideal (𝓞 K))⁰} {x : K} :
    x ∈ invBaseFrac 𝔡 ↔ x ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
  Iff.rfl

/-- The inverse of a nonzero integral ideal is an additive subgroup. -/
theorem add_mem_inv_coeIdeal (𝔡 : (Ideal (𝓞 K))⁰) {x y : K}
    (hx : x ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (hy : y ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    x + y ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
  Submodule.add_mem (invBaseFrac 𝔡 : Submodule (𝓞 K) K) hx hy

/-- Membership in the lattice implies membership in `𝔡⁻¹`. -/
theorem mem_inv_base_of_mem_magSet {𝔪 : Modulus K} {𝔡 : (Ideal (𝓞 K))⁰} {x : K}
    (hx : x ∈ ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) :
    x ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
  (magIdeal_le_inv_base 𝔪 𝔡) hx

/-- **An algebraic integer lies in `𝔪.ideal · 𝔡⁻¹` iff it lies in `𝔪.ideal`.** -/
theorem mem_magIdeal_iff_mem_ideal (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (z : 𝓞 K) :
    ((z : K) ∈ ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
      ↔ z ∈ 𝔪.ideal := by
  classical
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [RingOfIntegers.coe_eq_algebraMap, map_zero]
    constructor <;> intro _ <;> exact Submodule.zero_mem _
  have hz' : ((z : 𝓞 K) : K) ≠ 0 := by simpa using hz
  constructor
  · -- `z ∈ M` ⟹ `z ∈ 𝔪.ideal`
    intro hzM
    have hspan : Ideal.span {z} ≤ 𝔪.ideal := by
      refine NK.NUV2.RouteB.Sharp.ideal_le_of_count_le (I := Ideal.span {z}) (J := 𝔪.ideal)
        (by simpa [Ideal.span_singleton_eq_bot] using hz) 𝔪.ideal_ne_zero (fun v => ?_)
      rw [FractionalIdeal.coeIdeal_span_singleton, count_modulusIdeal,
        count_spanSingleton_eq v hz']
      by_cases hv : 𝔪.exps v ≠ 0
      · have h := (mem_iff_count_le (magIdeal_ne_zero 𝔪 𝔡) hz').mp hzM v
        rw [count_magIdeal_of_exp_ne_zero 𝔪 𝔡 hcop hv] at h
        exact h
      · rw [show 𝔪.exps v = 0 from not_not.mp hv, Nat.cast_zero]
        exact neg_log_valuation_nonneg v z
    exact hspan (Ideal.mem_span_singleton_self z)
  · -- `z ∈ 𝔪.ideal` ⟹ `z ∈ M`
    intro hzI
    refine (mem_iff_count_le (magIdeal_ne_zero 𝔪 𝔡) hz').mpr (fun v => ?_)
    by_cases hv : 𝔪.exps v ≠ 0
    · rw [count_magIdeal_of_exp_ne_zero 𝔪 𝔡 hcop hv]
      have hmem : z ∈ v.asIdeal ^ (𝔪.exps v) :=
        (NK.NUV2.RouteB.Sharp.finset_prod_le_pow_of_mem 𝔪.exps 𝔪.supportFinset
          (𝔪.mem_supportFinset hv)) (by rw [← Modulus.ideal]; exact hzI)
      exact le_neg_log_valuation_of_mem_pow v hz (𝔪.exps v) hmem
    · have hM : FractionalIdeal.count K v
          ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
          = -FractionalIdeal.count K v ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [count_magIdeal, show 𝔪.exps v = 0 from not_not.mp hv, Nat.cast_zero, zero_sub]
      rw [hM]
      exact le_trans (neg_le_neg (FractionalIdeal.count_coe_nonneg K v (𝔡 : Ideal (𝓞 K))))
        (neg_log_valuation_nonneg v z)

/-! ## The dictionary: congruence modulo `𝔪` versus membership in `𝔪.ideal · 𝔡⁻¹` -/

/-- One is an element of `𝔡⁻¹` for a nonzero integral ideal `𝔡`. -/
theorem one_mem_inv_coeIdeal (𝔡 : (Ideal (𝓞 K))⁰) :
    (1 : K) ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤
      ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
    one_le_inv_coeIdeal (𝔡 : Ideal (𝓞 K)) (baseIdeal_ne_zero 𝔡)
  exact h1 (by rw [FractionalIdeal.mem_one_iff]; exact ⟨1, map_one _⟩)

/-- Multiplication by a unit of `𝓞 K` preserves membership in a fractional ideal. -/
theorem unit_mul_mem_iff (M : FractionalIdeal (𝓞 K)⁰ K) (u : (𝓞 K)ˣ) {y : K} :
    (((u : 𝓞 K) : K) * y ∈ M) ↔ y ∈ M := by
  constructor
  · intro hy
    have hy' : ((u : 𝓞 K)) • y ∈ M := by simpa [Algebra.smul_def] using hy
    have h1 : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • (((u : 𝓞 K)) • y) ∈ M :=
      Submodule.smul_mem (M : Submodule (𝓞 K) K) ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) hy'
    have h2 : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • (((u : 𝓞 K)) • y) = y := by
      rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rwa [h2] at h1
  · intro hy
    have h1 : ((u : 𝓞 K)) • y ∈ M :=
      Submodule.smul_mem (M : Submodule (𝓞 K) K) ((u : 𝓞 K)) hy
    simpa [Algebra.smul_def] using h1

/-- **The dictionary.**  Let `𝔪` be a modulus with `𝔪.pos = ∅`, let `𝔡 ≠ 0` be an integral ideal
coprime to the support of `𝔪`, let `u` be a unit of `𝓞 K` and `β ∈ 𝔡⁻¹`.  Then `u · β` is
`≡ 1 (mod 𝔪)` (in the sense of `IsCongElem`) if and only if `β - u⁻¹` lies in the fractional ideal
`𝔪.ideal · 𝔡⁻¹`.  This is the correspondence between the congruence condition and the lattice
cosets used for the ray-class/lattice dictionary. -/
theorem isCongElem_mul_unit_iff_sub_mem_magIdeal (𝔪 : Modulus K) (hpos : 𝔪.pos = ∅)
    (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (u : (𝓞 K)ˣ) {β : K}
    (hβ : β ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    IsCongElem K 𝔪 (((u : 𝓞 K) : K) * β) ↔
      β - (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) ∈
        ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
  set 𝔡I : FractionalIdeal (𝓞 K)⁰ K := ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) with h𝔡I
  set M : FractionalIdeal (𝓞 K)⁰ K :=
    ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) with hM
  have hM0 : M ≠ 0 := magIdeal_ne_zero 𝔪 𝔡
  have hstep1 : (β - (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) ∈ M) ↔
      (((u : 𝓞 K) : K) * β - 1) ∈ M := by
    have hu : ((u : 𝓞 K) : K) ≠ 0 :=
      fun h => Units.ne_zero u (RingOfIntegers.coe_injective h)
    have hEq : ((u : 𝓞 K) : K) * β - 1
        = ((u : 𝓞 K) : K) * (β - (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) := by
      rw [mul_sub]
      congr 1
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rw [hEq]
    exact (unit_mul_mem_iff M u).symm
  -- `u β - 1` lies in `𝔡⁻¹`
  have hx_inv : (((u : 𝓞 K) : K) * β - 1) ∈ 𝔡I⁻¹ := by
    have huβ : ((u : 𝓞 K) : K) * β ∈ 𝔡I⁻¹ := by
      have h : ((u : 𝓞 K)) • β ∈ (((𝔡I)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
        Submodule.smul_mem (((𝔡I)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
          ((u : 𝓞 K)) hβ
      simpa [Algebra.smul_def] using h
    exact Submodule.sub_mem (((𝔡I)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) huβ
      (one_mem_inv_coeIdeal 𝔡)
  constructor
  · -- `≡ 1` modulo `𝔪` implies membership in the lattice
    intro hcong
    rw [hstep1]
    by_cases hx : ((u : 𝓞 K) : K) * β - 1 = 0
    · rw [hx]
      exact Submodule.zero_mem (M : Submodule (𝓞 K) K)
    · refine (mem_iff_count_le hM0 hx).mpr (fun q => ?_)
      by_cases hq : 𝔪.exps q ≠ 0
      · rw [count_magIdeal_of_exp_ne_zero 𝔪 𝔡 hcop hq]
        have hval : (q.valuation K) (((u : 𝓞 K) : K) * β - 1)
            ≤ WithZero.exp (-(𝔪.exps q : ℤ)) := by
          have h := hcong.1 q hq
          rwa [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq] at h
        have hne : (q.valuation K) (((u : 𝓞 K) : K) * β - 1) ≠ 0 :=
          (Valuation.ne_zero_iff _).mpr hx
        have hlog : ((q.valuation K) (((u : 𝓞 K) : K) * β - 1)).log ≤ -(𝔪.exps q : ℤ) := by
          have h := (WithZero.log_le_log hne
            (WithZero.exp_ne_zero (a := (-(𝔪.exps q : ℤ))))).mpr hval
          rwa [WithZero.log_exp] at h
        linarith
      · rw [count_magIdeal, show 𝔪.exps q = 0 from not_not.mp hq, Nat.cast_zero, zero_sub]
        have h1 : FractionalIdeal.count K q (𝔡I⁻¹)
            ≤ FractionalIdeal.count K q
              (FractionalIdeal.spanSingleton (𝓞 K)⁰ (((u : 𝓞 K) : K) * β - 1)) :=
          FractionalIdeal.count_mono K q
            (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
            (FractionalIdeal.spanSingleton_le_iff_mem.mpr hx_inv)
        rw [FractionalIdeal.count_inv, count_spanSingleton_eq q hx] at h1
        simpa using h1
  · -- membership in the lattice implies `≡ 1` modulo `𝔪`
    intro hmem
    have hxmem : (((u : 𝓞 K) : K) * β - 1) ∈ M := hstep1.mp hmem
    refine ⟨fun q hq => ?_, fun w hw hwpos => ?_⟩
    · by_cases hx : ((u : 𝓞 K) : K) * β - 1 = 0
      · rw [hx, map_zero]
        simp
      · have h := (mem_iff_count_le hM0 hx).mp hxmem q
        rw [count_magIdeal_of_exp_ne_zero 𝔪 𝔡 hcop hq] at h
        have hne : (q.valuation K) (((u : 𝓞 K) : K) * β - 1) ≠ 0 :=
          (Valuation.ne_zero_iff _).mpr hx
        have hlog : ((q.valuation K) (((u : 𝓞 K) : K) * β - 1)).log ≤ -(𝔪.exps q : ℤ) := by
          linarith
        have hval : (q.valuation K) (((u : 𝓞 K) : K) * β - 1)
            ≤ WithZero.exp (-(𝔪.exps q : ℤ)) := by
          rw [← WithZero.exp_log hne]
          exact WithZero.exp_le_exp.mpr hlog
        rwa [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
    · rw [hpos] at hwpos
      exact absurd hwpos (Set.notMem_empty w)

end NK.NUV2.RouteB.CongCount

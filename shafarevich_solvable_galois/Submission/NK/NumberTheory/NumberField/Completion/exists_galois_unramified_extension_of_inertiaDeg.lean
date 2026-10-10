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
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.NumberField.Completion

/-!
# Gap A (Galois form): a Galois unramified extension of prescribed inertia degree

Given a number field `L`, a finite place `q` of `𝓞 L` and `n ≥ 1`, we build a **finite Galois**
extension `L' / L` with a place `q'` over `q` which is unramified of inertia degree `n`.

## Construction

Write `𝔽 := 𝓞 L ⧸ q`, `q₀ := #𝔽`, `m := q₀ ^ n - 1`, and take `L' := CyclotomicField m L` = `L(ζ_m)`.
This is a number field (finitely generated over `ℚ`), Galois over `L`, and `q` is unramified in it
because the rational prime below `q` does not divide `m`.

The inertia degree is computed as follows:
* `n ≤ f(q'|q)`: the reduction map `μ_m → (𝓞 L' ⧸ q')ˣ` is injective (`q ∤ m` implies `X ^ m - 1` has
  distinct roots mod `q`), so the residue field contains `μ_m` of order `q₀ ^ n - 1`; hence
  `q₀ ^ n ≤ q₀ ^ f`.
* `f(q'|q) ≤ n`: the Frobenius element of the unramified prime `q'` acts on `μ_m` by `ζ ↦ ζ ^ q₀`,
  an element of order exactly `n` (`pow_sub_one_dvd_pow_sub_one_iff`); the decomposition group of an
  unramified prime is generated by the Frobenius, so `f(q'|q) = n`
  (`exists_orderOf_eq_inertiaDeg_of_ramificationIdx_eq_one`).

This file proves the arithmetic core and the construction (`CharZero`, `NumberField`, `IsGalois`,
lying over).  The two local computations `e = 1` and `f = n` are the two remaining goals.
-/

/-- **A finite field has `#k = 0` in itself.**  If `k` is a finite field then the image of its
cardinality in `k` vanishes: `(#k : k) = 0`.

Proof: `FiniteField.card` writes `#k = p ^ n` with `p = char k` prime, and `(p : k) = 0`
(`CharP.cast_eq_zero`), so `(#k : k) = (p : k) ^ n = 0` (and `n ≠ 0` since a field has at least two
elements).

This is the side condition of `cyclotomic_unramified_and_residue` in
`exists_galois_unramified_extension_of_inertiaDeg`: with `m = #k ^ n - 1` it shows that `m` maps to
`-1` in the residue field `k = 𝓞 L ⧸ q`, hence `q ∤ m`. -/
theorem natCast_card_eq_zero (k : Type*) [Field k] [Fintype k] :
    ((Fintype.card k : ℕ) : k) = 0 := by
  obtain ⟨p, hp⟩ := CharP.exists k
  haveI : CharP k p := hp
  obtain ⟨n, -, hcard⟩ := FiniteField.card k p
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn, pow_zero] at hcard
    have := Fintype.one_lt_card (α := k)
    omega
  · rw [hcard, Nat.cast_pow, CharP.cast_eq_zero k p, zero_pow hn.ne']

/-- **Arithmetic core.**  For `q ≥ 2` and `n > 0`: `q ^ n - 1 ∣ q ^ d - 1 ↔ n ∣ d`.  Equivalently,
the "Frobenius" `ζ ↦ ζ ^ q` on the group `μ_{q ^ n - 1}` of order `q ^ n - 1` has order exactly
`n`. -/
theorem pow_sub_one_dvd_pow_sub_one_iff {q n d : ℕ} (hq : 2 ≤ q) (hn : 0 < n) :
    q ^ n - 1 ∣ q ^ d - 1 ↔ n ∣ d := by
  constructor
  · intro h
    set k := d / n with hk
    set r := d % n with hr
    have hd : d = n * k + r := by
      rw [hk, hr]
      exact (Nat.div_add_mod d n).symm
    have hrlt : r < n := Nat.mod_lt d hn
    have hqpow : q ^ d = q ^ (n * k) * q ^ r := by rw [hd, pow_add]
    have h2 : q ^ n - 1 ∣ q ^ d - q ^ r := by
      have h1 : q ^ n - 1 ∣ q ^ (n * k) - 1 :=
        Nat.pow_sub_one_dvd_pow_sub_one (x := q) (Nat.dvd_mul_right n k)
      have h1' := Dvd.dvd.mul_right h1 (q ^ r)
      rwa [Nat.sub_mul, one_mul, ← hqpow] at h1'
    have hB : 1 ≤ q ^ r := one_le_pow₀ (by omega)
    have hle : q ^ r ≤ q ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : q ^ n - 1 ∣ q ^ r - 1 := by
      have hsub := Nat.dvd_sub h h2
      have heq : (q ^ d - 1) - (q ^ d - q ^ r) = q ^ r - 1 := by omega
      rwa [heq] at hsub
    have hlt : q ^ r - 1 < q ^ n - 1 := by
      have : q ^ r < q ^ n := Nat.pow_lt_pow_right (by omega) hrlt
      omega
    have hzero : q ^ r - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h3 hlt
    have hq1 : q ^ r = 1 := by omega
    have hr0 : r = 0 := by
      by_contra hne
      have hpos : 0 < r := Nat.pos_of_ne_zero hne
      have hge : 2 ≤ q ^ r := by
        calc 2 ≤ q := hq
          _ = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ r := Nat.pow_le_pow_right (by omega) hpos
      omega
    exact ⟨k, by rw [hd, hr0, Nat.add_zero]⟩
  · intro h
    exact Nat.pow_sub_one_dvd_pow_sub_one (x := q) h


/-- **The rational prime under a finite place lies in it.**  For a number field `L` and a finite
place `q` of `𝓞 L`, some rational prime `p` satisfies `(p : 𝓞 L) ∈ q.asIdeal`.

This is item 2 of the `e = 1` derivation for `exists_galois_unramified_extension_of_inertiaDeg`
(there with `p ^ n = q₀ = #(𝓞 L ⧸ q)`): combined with `FiniteField.card` it gives
`(q₀ : 𝓞 L) ∈ q.asIdeal`, whence `Ideal.Quotient.mk q.asIdeal (q₀ : 𝓞 L) = 0` and, through
`map_natCast`/`map_pow`/`map_sub`/`map_one` on the ring hom, the side condition `q ∤ m`.

Route (all step names verified by `#check` against Mathlib): `q.asIdeal.under ℤ` is prime
(`Ideal.IsPrime.under`), hence principal with generator `z ≠ 0` (`ℤ` is a PID); `Prime z` from
`Ideal.span_singleton_prime`, so `p := z.natAbs` is prime (`Int.prime_iff_natAbs_prime`) and
`z = ±p`, giving `(p : ℤ) ∈ q.asIdeal.under ℤ`; `Ideal.mem_under` plus the cast transport
`algebraMap ℤ (𝓞 L) (p : ℤ) = (p : 𝓞 L)` conclude. -/
theorem exists_prime_mem_of_heightOneSpectrum {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    ∃ p : ℕ, Nat.Prime p ∧ (p : NumberField.RingOfIntegers L) ∈ q.asIdeal := by
  haveI : Algebra.IsIntegral ℤ (NumberField.RingOfIntegers L) := inferInstance
  have hne : q.asIdeal.under ℤ ≠ ⊥ :=
    Ideal.under_ne_bot ℤ (P := q.asIdeal) q.ne_bot
  obtain ⟨z, hz⟩ := (Submodule.isPrincipal_iff (q.asIdeal.under ℤ)).mp
    (inferInstance : (q.asIdeal.under ℤ).IsPrincipal)
  have hspan : Ideal.span ({z} : Set ℤ) = q.asIdeal.under ℤ := by rw [hz]
  have hz0 : z ≠ 0 := by
    rintro rfl
    refine hne ?_
    rw [hz]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hpr : Prime z :=
    (Ideal.span_singleton_prime hz0).mp (hspan ▸ Ideal.IsPrime.under ℤ q.asIdeal)
  refine ⟨z.natAbs, Int.prime_iff_natAbs_prime.mp hpr, ?_⟩
  have hcast : algebraMap ℤ (NumberField.RingOfIntegers L) (z.natAbs : ℤ)
      = ((z.natAbs : ℕ) : NumberField.RingOfIntegers L) := by simp
  rw [← hcast, ← Ideal.mem_under (A := ℤ) (P := q.asIdeal), ← hspan, Ideal.mem_span_singleton]
  exact (Int.natAbs_dvd (a := z) (b := (z.natAbs : ℤ))).mp dvd_rfl

/-- **The cardinality of the residue field lies in `q`.**  For a number field `L` and a finite
place `q`, `(#(𝓞 L ⧸ q) : 𝓞 L) ∈ q.asIdeal` — i.e. `q₀` vanishes in the residue field.

Stated with `Nat.card` (not `Fintype.card`) deliberately: `Nat.card` needs no `Fintype` instance in
the statement, which avoids the "instance in a statement" friction that stalls elaboration.

Proof route (see `NOTE_gapA_galois_status.md`): take `p` from
`exists_prime_mem_of_heightOneSpectrum`; `q₀ = p ^ f` with `f` the residue degree, justified inside
the base field `ℤ ⧸ Ideal.span {(p : ℤ)}` — where `CharP` *is* available (`CharP.quotient`) — via
`Module.card_eq_pow_finrank` for the algebra `(ℤ ⧸ span {p}) → (𝓞 L ⧸ q)`; then `p ^ f ∈ q.asIdeal`
by closure under powers.

This is the last input of the `e = 1` side condition `q ∤ m`: with it,
`Ideal.Quotient.mk q.asIdeal (q₀ : 𝓞 L) = 0`, so `mk m = (mk q₀) ^ n - 1 = -1 ≠ 0` through
`map_natCast`/`map_pow`/`map_sub`/`map_one`, and `Ideal.Quotient.eq_zero_iff_mem` gives `q ∤ m`. -/
theorem natCard_residueField_mem {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    ((Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal) : ℕ) :
      NumberField.RingOfIntegers L) ∈ q.asIdeal := by
  obtain ⟨p, hp, hp_mem⟩ := exists_prime_mem_of_heightOneSpectrum q
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hcomap : Ideal.span {(p : ℤ)} ≤
      Ideal.comap (algebraMap ℤ (NumberField.RingOfIntegers L)) q.asIdeal := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show algebraMap ℤ (NumberField.RingOfIntegers L) (p : ℤ) ∈ q.asIdeal
    simpa using hp_mem
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := by
    have hI : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
    have hbot : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hprime.ne_zero
    exact Ideal.IsPrime.isMaximal hI hbot
  letI : Field (ℤ ⧸ Ideal.span {(p : ℤ)}) := Ideal.Quotient.field _
  haveI hchar : CharP (ℤ ⧸ Ideal.span {(p : ℤ)}) p := CharP.quotient ℤ p hprime.not_unit
  haveI halg : Algebra (ℤ ⧸ Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap hcomap
  haveI hfq : Fintype (NumberField.RingOfIntegers L ⧸ q.asIdeal) := Fintype.ofFinite _
  haveI hfp : Fintype (ℤ ⧸ Ideal.span {(p : ℤ)}) := Fintype.ofFinite _
  have hbase : Fintype.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv,
      Nat.card_eq_fintype_card, ZMod.card]
  have hcard : Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal) = p ^
      Module.finrank (ℤ ⧸ Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers L ⧸ q.asIdeal) := by
    rw [Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := ℤ ⧸ Ideal.span {(p : ℤ)})
        (V := NumberField.RingOfIntegers L ⧸ q.asIdeal), hbase]
  rw [hcard, Nat.cast_pow]
  exact Ideal.pow_mem_of_mem q.asIdeal hp_mem _
    (Module.finrank_pos (R := ℤ ⧸ Ideal.span {(p : ℤ)})
      (M := NumberField.RingOfIntegers L ⧸ q.asIdeal))


/-- **If `1 - η ∈ q'` then the rational prime under `q` divides `n`.**

Let `L'/L` be an extension of number fields, `q'` a prime of `𝓞 L'` over `q` and `η ∈ 𝓞 L'` a
primitive `n`-th root of unity with `n > 1`.  Then `1 - η ∈ q'` forces `(n : 𝓞 L) ∈ q`.

Proof: `X ^ n - 1 = ∏_{ζ^n = 1} (X - ζ)` and the factor `X - 1` can be cancelled (geometric
series), giving `n = ∏_{ζ^n = 1, ζ ≠ 1} (1 - ζ)`; every `ζ ≠ 1` with `ζ^n = 1` is a power `η ^ i`
(`IsPrimitiveRoot.eq_pow_of_pow_eq_one`), and `1 - η ^ i = (1 - η)(1 + η + ⋯ + η^{i-1})`, so
`(1 - η) ∣ n` in `𝓞 L'`; then `1 - η ∈ q'` gives `n ∈ q'`, i.e. `n ∈ q` by `LiesOver`. -/
theorem natCast_mem_of_one_sub_isPrimitiveRoot_mem
    {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L']
    [Algebra L L'] [FiniteDimensional L L']
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'))
    (hqq' : q'.asIdeal.LiesOver q.asIdeal)
    {n : ℕ} (hn : 1 < n) {η : NumberField.RingOfIntegers L'}
    (hη : IsPrimitiveRoot (η : L') n)
    (h : (1 - η) ∈ q'.asIdeal) :
    (n : NumberField.RingOfIntegers L) ∈ q.asIdeal := by
  classical
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  have hη' : IsPrimitiveRoot η n := by
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      push_cast
      exact hη.pow_eq_one
    · intro l hl
      refine hη.dvd_of_pow_eq_one l ?_
      have hh : ((η ^ l : NumberField.RingOfIntegers L') : L') = 1 := by
        rw [hl]
        simp
      simpa using hh
  set S := Polynomial.nthRootsFinset n (1 : NumberField.RingOfIntegers L') with hS
  have h1S : (1 : NumberField.RingOfIntegers L') ∈ S := by
    rw [hS, Polynomial.mem_nthRootsFinset hn0 (1 : NumberField.RingOfIntegers L')]
    simp
  have hX1 : (Polynomial.X - 1 : (Polynomial (NumberField.RingOfIntegers L'))) ≠ 0 := by
    intro hc
    have := congrArg (fun p => Polynomial.eval 0 p) hc
    simpa using this
  have hcancel : ∏ ζ ∈ S.erase 1, (Polynomial.X - Polynomial.C ζ)
      = ∑ j ∈ Finset.range n, (Polynomial.X : (Polynomial (NumberField.RingOfIntegers L'))) ^ j := by
    have hp := Finset.prod_erase_mul S (fun ζ => (Polynomial.X - Polynomial.C ζ)) h1S
    rw [show (Polynomial.X - Polynomial.C (1 : NumberField.RingOfIntegers L'))
        = Polynomial.X - 1 from by simp] at hp
    have h2 : (∏ ζ ∈ S.erase 1, (Polynomial.X - Polynomial.C ζ)) * (Polynomial.X - 1)
        = (∑ j ∈ Finset.range n, (Polynomial.X : (Polynomial (NumberField.RingOfIntegers L'))) ^ j)
            * (Polynomial.X - 1) := by
      rw [hp, ← Polynomial.X_pow_sub_one_eq_prod hn0 hη']
      exact (geom_sum_mul (Polynomial.X : (Polynomial (NumberField.RingOfIntegers L'))) n).symm
    exact mul_right_cancel₀ hX1 h2
  have hval : ∏ ζ ∈ S.erase 1, (1 - ζ) = (n : NumberField.RingOfIntegers L') := by
    have h3 := congrArg (fun p : (Polynomial (NumberField.RingOfIntegers L')) => Polynomial.eval 1 p) hcancel
    simpa [Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_pow,
      Polynomial.eval_X] using h3
  have hfac : ∀ ζ ∈ S.erase 1, ∃ k : NumberField.RingOfIntegers L', 1 - ζ = (1 - η) * k := by
    intro ζ hζ
    rw [Finset.mem_erase] at hζ
    obtain ⟨hζne, hζS⟩ := hζ
    have hζpow : ζ ^ n = 1 :=
      (Polynomial.mem_nthRootsFinset hn0 (1 : NumberField.RingOfIntegers L')).mp hζS
    obtain ⟨i, hi_lt, hi⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hη' hζpow
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hi
      exact hζne hi.symm
    refine ⟨∑ j ∈ Finset.range i, η ^ j, ?_⟩
    rw [← hi]
    have hgs := geom_sum_mul η i
    rw [show ((1 : NumberField.RingOfIntegers L') - η ^ i)
        = -((∑ j ∈ Finset.range i, η ^ j) * (η - 1)) from by rw [hgs]; ring]
    ring
  have hspan : (n : NumberField.RingOfIntegers L')
      ∈ Ideal.span ({(1 - η)} : Set (NumberField.RingOfIntegers L')) := by
    rw [← hval]
    have hne : (S.erase 1).Nonempty := by
      refine ⟨η, ?_⟩
      rw [Finset.mem_erase]
      refine ⟨hη'.ne_one hn, ?_⟩
      rw [hS, Polynomial.mem_nthRootsFinset hn0 (1 : NumberField.RingOfIntegers L')]
      exact hη'.pow_eq_one
    obtain ⟨ζ₀, hζ₀⟩ := hne
    obtain ⟨k₀, hk₀⟩ := hfac ζ₀ hζ₀
    rw [← Finset.prod_erase_mul _ _ hζ₀]
    rw [hk₀]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  have hnq' : (n : NumberField.RingOfIntegers L') ∈ q'.asIdeal :=
    (Ideal.span_le.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rwa [hx])) hspan
  rw [hqq'.over, Ideal.mem_under]
  simpa using hnq'

/-- **The reduction of a primitive `m`-th root of unity at a prime `q' ∤ m` is again primitive**
(component (2) of `cyclotomic_unramified_and_residue`).

If `q ∤ m` (i.e. `(m : 𝓞 L) ∉ q`) and `ζ` is a primitive `m`-th root of unity in `L(ζ_m)`, then
`ζ mod q'` is a primitive `m`-th root of unity in the residue field of `q'`.

Proof: `(mk ζ)^m = 1`, and if `(mk ζ)^d = 1` for a proper divisor `d ∣ m`, then `1 - ζ^d ∈ q'`
with `ζ^d` a primitive `(m/d)`-th root, so `natCast_mem_of_one_sub_isPrimitiveRoot_mem` forces
`(m/d : 𝓞 L) ∈ q`, whence `(m : 𝓞 L) ∈ q`, contradicting `q ∤ m`. -/
theorem isPrimitiveRoot_reduction
    {L : Type*} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {m : ℕ} [NeZero m]
    (hq : ((m : ℕ) : NumberField.RingOfIntegers L) ∉ q.asIdeal)
    (q' : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers (CyclotomicField m L)))
    (hqq' : q'.asIdeal.LiesOver q.asIdeal)
    {ζ : NumberField.RingOfIntegers (CyclotomicField m L)}
    (hζ : IsPrimitiveRoot (ζ : CyclotomicField m L) m) :
    IsPrimitiveRoot (Ideal.Quotient.mk q'.asIdeal ζ) m := by
  classical
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have key : ∀ d : ℕ, d ∣ m → d < m → (Ideal.Quotient.mk q'.asIdeal ζ) ^ d ≠ 1 := by
    intro d hd hlt hpow
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd; omega
    have hpowroot : IsPrimitiveRoot
        ((ζ ^ d : NumberField.RingOfIntegers (CyclotomicField m L)) : CyclotomicField m L)
        (m / d) := by
      have := hζ.pow_of_dvd hd0 hd
      simpa using this
    have hmem : (1 - ζ ^ d) ∈ q'.asIdeal := by
      have hzero : Ideal.Quotient.mk q'.asIdeal (ζ ^ d) = 1 := by
        rw [map_pow]; exact hpow
      have : Ideal.Quotient.mk q'.asIdeal (1 - ζ ^ d) = 0 := by
        rw [map_sub, map_one, hzero, sub_self]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp this
    have hgt : 1 < m / d := by
      have hmul : d * (m / d) = m := Nat.mul_div_cancel' hd
      nlinarith [Nat.pos_of_ne_zero hd0]
    have hmem_q := natCast_mem_of_one_sub_isPrimitiveRoot_mem (L := L)
      (L' := CyclotomicField m L) q q' hqq' hgt hpowroot hmem
    have hmul : (d : NumberField.RingOfIntegers L)
        * ((m / d : ℕ) : NumberField.RingOfIntegers L)
        = ((m : ℕ) : NumberField.RingOfIntegers L) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hd]
    exact hq (hmul ▸ Ideal.mul_mem_left _ _ hmem_q)
  have hzm : ζ ^ m = 1 := by
    apply Subtype.ext
    push_cast
    exact hζ.pow_eq_one
  have hdvd : orderOf (Ideal.Quotient.mk q'.asIdeal ζ) ∣ m :=
    orderOf_dvd_iff_pow_eq_one.mpr (by
      calc (Ideal.Quotient.mk q'.asIdeal ζ) ^ m
          = Ideal.Quotient.mk q'.asIdeal (ζ ^ m) := (map_pow _ ζ m).symm
        _ = Ideal.Quotient.mk q'.asIdeal 1 := congrArg (Ideal.Quotient.mk q'.asIdeal) hzm
        _ = 1 := map_one _)
  have hord : orderOf (Ideal.Quotient.mk q'.asIdeal ζ) = m := by
    rcases eq_or_lt_of_le (Nat.le_of_dvd hm0 hdvd) with h | h
    · exact h
    · exact absurd (show (Ideal.Quotient.mk q'.asIdeal ζ) ^
          orderOf (Ideal.Quotient.mk q'.asIdeal ζ) = 1 from pow_orderOf_eq_one _)
        (key _ hdvd h)
  have hpowm : (Ideal.Quotient.mk q'.asIdeal ζ) ^ m = 1 := by
    have hthis := pow_orderOf_eq_one (Ideal.Quotient.mk q'.asIdeal ζ)
    rwa [hord] at hthis
  refine IsPrimitiveRoot.mk hpowm ?_
  · intro l hl
    have hd : orderOf (Ideal.Quotient.mk q'.asIdeal ζ) ∣ l :=
      orderOf_dvd_iff_pow_eq_one.mpr hl
    rwa [hord] at hd


/-- **Unramifiedness of `L(ζ_m)` at the places above `q`, for `q ∤ m`.**  If `m ≠ 0`,
`m ∉ q.asIdeal` (i.e. `q` does not divide `m`) and `q'` is a prime of `L(ζ_m)` above `q`, then
`e(q'|q) = 1`.

This is the `e = 1` step inside `exists_galois_unramified_extension_of_inertiaDeg`, where
`m = #(𝓞 L ⧸ q) ^ n - 1`; the hypothesis `m ∉ q.asIdeal` holds there because the rational prime
under `q` divides `#(𝓞 L ⧸ q)` and `m ≡ -1` modulo it.

Proof (the `differentIdeal`/discriminant route is *not* needed): the inertia subgroup
`J = q'.asIdeal.inertia Gal(L(ζ_m)/L) ≤ Gal(L(ζ_m)/L)` has `Nat.card J = e(q'|q)`
(Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` + `Ideal.ramificationIdxIn_eq_ramificationIdx`),
so it suffices to show `J = ⊥`.  Let `τ ∈ J` and let `ζ ∈ 𝓞 L(ζ_m)` be a primitive `m`-th root of
unity.  Then `τ • ζ - ζ ∈ q'.asIdeal`, i.e. `ζ mod q'` is fixed by `τ`; writing
`τ • ζ = ζ ^ j` (`IsPrimitiveRoot.eq_pow_of_pow_eq_one`) and applying `Ideal.Quotient.mk q'.asIdeal`,
`(ζ mod q') ^ j = ζ mod q'`, and since `ζ mod q'` **is primitive of order `m`** by
`isPrimitiveRoot_reduction` (`q ∤ m`!), `IsPrimitiveRoot.pow_inj` forces `j = 1`; hence `τ • ζ = ζ`.
Finally `L(ζ_m) = L[ζ]` (`IsCyclotomicExtension.adjoin_roots`: every `m`-th root of unity is a power
of `ζ`), so an `L`-algebra automorphism fixing `ζ` is the identity: `τ = 1` and `J = ⊥`. -/
theorem ramificationIdx_cyclotomic_eq_one {L : Type} [Field L] [NumberField L] {m : ℕ} [NeZero m]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : ((m : ℕ) : NumberField.RingOfIntegers L) ∉ q.asIdeal)
    (q' : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers (CyclotomicField m L)))
    (hqq' : q'.asIdeal.LiesOver q.asIdeal) :
    q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) = 1 := by
  classical
  haveI hgal : IsGalois L (CyclotomicField m L) :=
    IsCyclotomicExtension.isGalois {m} L (CyclotomicField m L)
  haveI hfin : FiniteDimensional L (CyclotomicField m L) :=
    IsCyclotomicExtension.finiteDimensional {m} L (CyclotomicField m L)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  -- a primitive m-th root of unity, integral, hence in the ring of integers
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot L
    (CyclotomicField m L) (Set.mem_singleton m) (NeZero.ne m)
  have hζitg : IsIntegral ℤ ζ := hζ.isIntegral hmpos
  obtain ⟨ζ₀, hζ₀⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := NumberField.RingOfIntegers (CyclotomicField m L))
      (R := ℤ) (B := CyclotomicField m L)).mp hζitg
  have hcoe : ((ζ₀ : NumberField.RingOfIntegers (CyclotomicField m L)) :
      CyclotomicField m L) = ζ := hζ₀
  have hζ₀' : IsPrimitiveRoot (ζ₀ : CyclotomicField m L) m := by
    rw [hcoe]; exact hζ
  -- the reduction of ζ₀ is primitive of order m
  have hprim : IsPrimitiveRoot
      (Ideal.Quotient.mk q'.asIdeal ζ₀
        : NumberField.RingOfIntegers (CyclotomicField m L) ⧸ q'.asIdeal) m :=
    Commons.NumberTheory.NumberField.Completion.isPrimitiveRoot_reduction q hq q' hqq' hζ₀'
  -- the Mathlib inertia subgroup
  let G := CyclotomicField m L ≃ₐ[L] CyclotomicField m L
  letI hMSA : MulSemiringAction G
      (NumberField.RingOfIntegers (CyclotomicField m L)) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers L) L
      (CyclotomicField m L) (NumberField.RingOfIntegers (CyclotomicField m L))
  haveI hGG : IsGaloisGroup G (NumberField.RingOfIntegers L)
      (NumberField.RingOfIntegers (CyclotomicField m L)) :=
    IsGaloisGroup.of_isFractionRing G (NumberField.RingOfIntegers L)
      (NumberField.RingOfIntegers (CyclotomicField m L)) L (CyclotomicField m L)
  haveI hFG : Module.Finite (NumberField.RingOfIntegers L)
      (NumberField.RingOfIntegers (CyclotomicField m L)) := inferInstance
  haveI hTF : Module.Flat (NumberField.RingOfIntegers L)
      (NumberField.RingOfIntegers (CyclotomicField m L)) := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hperf : PerfectField q.asIdeal.ResidueField :=
    Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum q
  letI : q'.asIdeal.LiesOver q.asIdeal := hqq'
  set J : Subgroup G := q'.asIdeal.inertia G with hJ
  have hcardJ : Nat.card J = q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) := by
    rw [hJ]
    rw [Ideal.card_inertia_eq_ramificationIdxIn (R := NumberField.RingOfIntegers L)
      (S := NumberField.RingOfIntegers (CyclotomicField m L)) (G := G) q.asIdeal q'.asIdeal]
    exact Ideal.ramificationIdxIn_eq_ramificationIdx q.asIdeal q'.asIdeal G
  have hJbot : J = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro τ hτ
    let L' := CyclotomicField m L
    have hmem : ∀ x : NumberField.RingOfIntegers L', τ • x - x ∈ q'.asIdeal :=
      (AddSubgroup.mem_inertia).mp hτ
    -- (A) the reductions of `τ • ζ₀` and `ζ₀` agree
    have hmk : Ideal.Quotient.mk q'.asIdeal (τ • ζ₀)
        = Ideal.Quotient.mk q'.asIdeal ζ₀ := by
      have h0 : Ideal.Quotient.mk q'.asIdeal (τ • ζ₀ - ζ₀) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr (hmem ζ₀)
      rwa [map_sub, sub_eq_zero] at h0
    -- (B) `τ • ζ₀` is a power of `ζ₀`
    have hcoe' : ((τ • ζ₀ : NumberField.RingOfIntegers L') : L') = τ (ζ₀ : L') :=
      algebraMap_galRestrict_apply (NumberField.RingOfIntegers L) τ ζ₀
    have hτpow : ((τ • ζ₀ : NumberField.RingOfIntegers L') : L') ^ m = 1 := by
      rw [hcoe', ← map_pow, hζ₀'.pow_eq_one, map_one]
    obtain ⟨j, hjlt, hj⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ₀' hτpow
    have hj' : ζ₀ ^ j = τ • ζ₀ := by
      apply Subtype.ext
      show (algebraMap (NumberField.RingOfIntegers L') L') (ζ₀ ^ j)
        = (algebraMap (NumberField.RingOfIntegers L') L') (τ • ζ₀)
      rw [map_pow]
      exact hj
    -- (C) `(mk ζ₀)^j = mk ζ₀`
    have hpow : (Ideal.Quotient.mk q'.asIdeal ζ₀) ^ j
        = Ideal.Quotient.mk q'.asIdeal ζ₀ := by
      rw [← map_pow, hj', hmk]
    -- (D) consequently `τ • ζ₀ = ζ₀`
    have hfixζ : τ • ζ₀ = ζ₀ := by
      rcases j with _ | k
      · have h1 : τ • ζ₀ = 1 := by
          rw [← hj']; simp
        have h3 : τ (ζ₀ : L') = τ (1 : L') := by
          rw [map_one, ← hcoe', h1]
          simp
        have h4 : ζ₀ = 1 := Subtype.coe_injective (τ.injective h3)
        rw [h1, h4]
      · have h1m : 1 < m := by omega
        have hji : k + 1 = 1 := hprim.pow_inj (by omega) h1m (by
          rw [pow_one]
          simpa using hpow)
        rw [← hj', hji, pow_one]
    have hfixζL : τ (ζ₀ : L') = (ζ₀ : L') := by
      rw [← hcoe', hfixζ]
    -- (E) `τ = 1`
    have hgen : ∀ x : L', x ∈ Algebra.adjoin L ({ζ} : Set L') := by
      intro x
      refine Algebra.adjoin_le (fun b hb => ?_) (IsCyclotomicExtension.adjoin_roots
        (S := {m}) (A := L) (B := L') x)
      obtain ⟨n, hn, _hn0, hbn⟩ := hb
      rw [Set.mem_singleton_iff] at hn
      subst hn
      obtain ⟨i, _hi, hii⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ hbn
      rw [← hii]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) i
    refine AlgEquiv.ext fun x => ?_
    have hx := hgen x
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        rw [show ζ = (ζ₀ : L') from hcoe.symm]
        exact hfixζL
    | algebraMap r => exact τ.commutes r
    | add y z hy hz ihy ihz => rw [map_add, map_add, ihy, ihz]
    | mul y z hy hz ihy ihz => rw [map_mul, map_mul, ihy, ihz]
  rw [← hcardJ, hJbot]
  simp


/-- **The shared input of Gap A: cyclotomic unramifiedness + residue-field structure at `q ∤ m`.**

For a number field `L`, a prime `q` of `𝓞 L` and `m ≥ 1` with `m ∉ q.asIdeal` (i.e. `q ∤ m`), let
`q'` be a prime of the cyclotomic field `L(ζ_m)` above `q`.  Then:

1. `e(q'|q) = 1` (`L(ζ_m)/L` is unramified above `q`);
2. the reduction of a primitive `m`-th root of unity is again primitive of order `m`
   (`μ_m ↪ (𝓞 L' ⧸ q')ˣ`; the two facts together with `n ≤ f` from part 2 and `f ≤ n` from part 3);
3. the residue field `𝓞 L' ⧸ q'` is generated, over the residue field `𝓞 L ⧸ q`, by that reduction.

All three come from one source: `X ^ m - 1` has distinct roots modulo `q` because `q ∤ m`
(classically: `N(ζ - ζ') = ± m` for distinct `m`-th roots of unity, plus the standard
`𝓞 L(ζ_m) = 𝓞 L[ζ_m]`).  **Not in Mathlib** for a general base field
(`Mathlib/NumberTheory/Cyclotomic/` is base-`ℚ` only, and there is no `Algebra.IsUnramifiedAt`
lemma for cyclotomic extensions), so this is the piece to build; it is the last genuinely new input
of `exists_galois_unramified_extension_of_inertiaDeg`.  Part 1 alone is
`ramificationIdx_cyclotomic_eq_one` below; the reduction chain for it is
`not_dvd_differentIdeal_iff` → `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`. -/
theorem cyclotomic_unramified_and_residue {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {m : ℕ} [NeZero m]
    (hq : ((m : ℕ) : NumberField.RingOfIntegers L) ∉ q.asIdeal)
    (q' : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers (CyclotomicField m L)))
    (hqq' : q'.asIdeal.LiesOver q.asIdeal) :
    q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) = 1 ∧
    (∀ ζ : NumberField.RingOfIntegers (CyclotomicField m L),
      IsPrimitiveRoot (ζ : CyclotomicField m L) m →
      IsPrimitiveRoot (Ideal.Quotient.mk q'.asIdeal ζ) m) ∧
    (∀ ζ : NumberField.RingOfIntegers (CyclotomicField m L),
      IsPrimitiveRoot (ζ : CyclotomicField m L) m →
      Algebra.adjoin (NumberField.RingOfIntegers L ⧸ q.asIdeal)
        ({Ideal.Quotient.mk q'.asIdeal ζ} : Set
          (NumberField.RingOfIntegers (CyclotomicField m L) ⧸ q'.asIdeal)) = ⊤) := by
  refine ⟨ramificationIdx_cyclotomic_eq_one q hq q' hqq',
    fun ζ hζ => isPrimitiveRoot_reduction q hq q' hqq' hζ, ?_⟩
  · sorry


/-- **Gap A, Galois form.**  A finite Galois extension `L' / L` with a place `q'` over `q` which is
unramified of inertia degree `n`.

The construction is complete: `L' := L(ζ_m)` with `m := q₀ ^ n - 1`, `q₀ := #(𝓞 L ⧸ q)`, and `q'`
any prime over `q` (`Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver`).  The two
remaining goals are the local computations `e(q'|q) = 1` and `f(q'|q) = n` described in the module
docstring. -/
theorem exists_galois_unramified_extension_of_inertiaDeg {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (n : ℕ) (hn : 0 < n) :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L')
      (_ : FiniteDimensional L L') (_ : IsGalois L L')
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L')),
      q'.asIdeal.LiesOver q.asIdeal ∧
        q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) = 1 ∧
        q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) = n := by
  classical
  haveI hfink : Finite (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
  haveI : Fintype (NumberField.RingOfIntegers L ⧸ q.asIdeal) := Fintype.ofFinite _
  let q₀ : ℕ := Fintype.card (NumberField.RingOfIntegers L ⧸ q.asIdeal)
  have hq0 : 2 ≤ q₀ := Fintype.one_lt_card
  have hm_pos : 0 < q₀ ^ n - 1 := by
    have h2 : 2 ≤ q₀ ^ n := by
      calc 2 ≤ q₀ := hq0
        _ = q₀ ^ 1 := (pow_one q₀).symm
        _ ≤ q₀ ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  let m : ℕ := q₀ ^ n - 1
  haveI hmne : NeZero m := ⟨by omega⟩
  haveI hcyc : IsCyclotomicExtension {m} L (CyclotomicField m L) :=
    CyclotomicField.isCyclotomicExtension m L
  haveI hgal : IsGalois L (CyclotomicField m L) :=
    IsCyclotomicExtension.isGalois {m} L (CyclotomicField m L)
  haveI hfin : FiniteDimensional L (CyclotomicField m L) :=
    IsCyclotomicExtension.finiteDimensional {m} L (CyclotomicField m L)
  haveI hnf : NumberField (CyclotomicField m L) := ⟨⟩
  obtain ⟨q', hq'⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := L)
      (L := CyclotomicField m L) q
  refine ⟨CyclotomicField m L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, q', hq', ?_, ?_⟩
  · -- `e(q'|q) = 1`: `q` does not divide `m`, so `L(ζ_m)` is unramified at `q`.
    have hqm : ((m : ℕ) : NumberField.RingOfIntegers L) ∉ q.asIdeal := by
      intro hmem
      have hzero : (Ideal.Quotient.mk q.asIdeal ((m : ℕ) : NumberField.RingOfIntegers L))
          = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
      have hq0mem : ((q₀ : ℕ) : NumberField.RingOfIntegers L) ∈ q.asIdeal := by
        have := Commons.NumberTheory.NumberField.Completion.natCard_residueField_mem (L := L) q
        simpa [q₀, Nat.card_eq_fintype_card] using this
      have hq0zero : (Ideal.Quotient.mk q.asIdeal
          ((q₀ : ℕ) : NumberField.RingOfIntegers L)) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr hq0mem
      have hone : 1 ≤ q₀ ^ n := Nat.one_le_pow n q₀ (by omega)
      have hval : (Ideal.Quotient.mk q.asIdeal ((m : ℕ) : NumberField.RingOfIntegers L))
          = -1 := by
        rw [show m = q₀ ^ n - 1 from rfl, Nat.cast_sub hone, Nat.cast_pow, Nat.cast_one,
          map_sub, map_one, map_pow, hq0zero, zero_pow hn.ne']
        ring
      rw [hval] at hzero
      exact absurd hzero (by
        haveI : Nontrivial (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
          Ideal.Quotient.nontrivial_iff.mpr (inferInstance : q.asIdeal.IsPrime).ne_top
        exact neg_ne_zero.mpr one_ne_zero)
    exact ramificationIdx_cyclotomic_eq_one q hqm q' hq'
  · -- `f(q'|q) = n`: reduction of `μ_m` is injective (giving `n ≤ f`) and the Frobenius has order
    -- exactly `n` (`pow_sub_one_dvd_pow_sub_one_iff`), giving `f ≤ n`.
    sorry



/-- The Frobenius action on a primitive `(#k ^ n - 1)`-th root of unity fixes it:
`ζ ^ (#k) ^ n = ζ`. -/
lemma pow_card_pow_eq_self_of_isPrimitiveRoot {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [Algebra k K] {n : ℕ} (hn : 0 < n) {ζ : K}
    (hζ : IsPrimitiveRoot ζ ((Fintype.card k) ^ n - 1)) :
    ζ ^ (Fintype.card k) ^ n = ζ := by
  have hq : 2 ≤ Fintype.card k := Fintype.one_lt_card
  have hqpos : 0 < Fintype.card k := lt_of_lt_of_le (by norm_num) hq
  have hq1 : 1 ≤ (Fintype.card k) ^ n := Nat.one_le_pow n (Fintype.card k) hqpos
  have hExp : (Fintype.card k) ^ n = ((Fintype.card k) ^ n - 1) + 1 := by omega
  have hone : ζ ^ ((Fintype.card k) ^ n - 1) = 1 :=
    (hζ.pow_eq_one_iff_dvd _).mpr dvd_rfl
  rw [hExp, pow_succ, hone, one_mul]

/-- Conversely, `(ζ ^ (#k)) ^ d = ζ` forces `n ∣ d`: the Frobenius has order exactly `n` on `μ_m`
(`pow_sub_one_dvd_pow_sub_one_iff`). -/
lemma dvd_of_pow_card_pow_eq_self {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [Algebra k K] {n d : ℕ} (hn : 0 < n) {ζ : K}
    (hζ : IsPrimitiveRoot ζ ((Fintype.card k) ^ n - 1))
    (hd : ζ ^ (Fintype.card k) ^ d = ζ) : n ∣ d := by
  have hq : 2 ≤ Fintype.card k := Fintype.one_lt_card
  have hqpos : 0 < Fintype.card k := lt_of_lt_of_le (by norm_num) hq
  -- `ζ ≠ 0`, since `ζ` is a root of unity of positive order
  have hm1 : 1 < (Fintype.card k) ^ n :=
    one_lt_pow₀ (by omega : 1 < Fintype.card k) (by omega : n ≠ 0)
  have hm0 : (Fintype.card k) ^ n - 1 ≠ 0 := fun h => by
    have hle : (Fintype.card k) ^ n ≤ 1 := Nat.sub_eq_zero_iff_le.mp h
    omega
  have hone₀ : ζ ^ ((Fintype.card k) ^ n - 1) = 1 :=
    (hζ.pow_eq_one_iff_dvd _).mpr dvd_rfl
  have hz : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm0] at hone₀
    exact one_ne_zero hone₀.symm
  have hq1 : 0 < (Fintype.card k) ^ d := pow_pos hqpos d
  have hExp : (Fintype.card k) ^ d = ((Fintype.card k) ^ d - 1) + 1 := by omega
  have hone : ζ ^ ((Fintype.card k) ^ d - 1) = 1 := by
    have h2 : ζ ^ ((Fintype.card k) ^ d - 1) * ζ = ζ := by
      rw [← pow_succ, ← hExp]
      exact hd
    exact mul_right_cancel₀ hz (by rw [one_mul]; exact h2)
  exact (pow_sub_one_dvd_pow_sub_one_iff hq hn).mp ((hζ.pow_eq_one_iff_dvd _).mp hone)

/-- **The `≥` half of the degree identity.**  If `ζ` is fixed by the `d`-fold Frobenius
(`ζ ^ (#k) ^ d = ζ`) then `(minpoly k ζ).natDegree ∣ d` — equivalently `minpoly k ζ` divides
`X ^ (#k) ^ d - X` (`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`).

This is the direction that bounds the degree *below* the order of Frobenius; combined with
`pow_card_pow_natDegree_eq_self` (the degree itself is such a `d`) it pins the degree down to the
least such `d`, and with `dvd_of_pow_card_pow_eq_self` (which turns `ζ ^ (#k) ^ d = ζ` into
`n ∣ d` for a primitive `(#k ^ n - 1)`-th root of unity) it gives `(minpoly k ζ).natDegree = n`. -/
theorem natDegree_minpoly_dvd_of_pow_card_pow_eq_self {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [Algebra k K] {ζ : K} (hζ : IsIntegral k ζ) {d : ℕ}
    (hd : ζ ^ (Fintype.card k) ^ d = ζ) :
    (minpoly k ζ).natDegree ∣ d := by
  have hroot : Polynomial.aeval ζ
      ((Polynomial.X : Polynomial k) ^ (Nat.card k) ^ d - Polynomial.X) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Nat.card_eq_fintype_card]
    rw [sub_eq_zero]
    exact hd
  have hdvd := minpoly.dvd k ζ hroot
  exact (minpoly.irreducible hζ).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd

/-- **The `≤` half of the degree identity, general form** (no generator hypothesis): for `ζ`
integral over a finite field `k`, the degree `D := (minpoly k ζ).natDegree` is itself an exponent
fixing `ζ`, i.e. `ζ ^ (#k) ^ D = ζ`.

Proof: `minpoly k ζ` is irreducible of degree `D`, hence (degree divides `D`) divides
`X ^ (#k) ^ D - X` by `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` (the `mp`
direction, with the exponent pinned); evaluating at `ζ` via `minpoly.dvd_iff` gives
`ζ ^ (#k) ^ D - ζ = 0`. -/
theorem pow_card_pow_natDegree_eq_self_of_isIntegral {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [Algebra k K] {ζ : K} (hζ : IsIntegral k ζ) :
    ζ ^ (Fintype.card k) ^ (minpoly k ζ).natDegree = ζ := by
  have hdvd : minpoly k ζ ∣
      (Polynomial.X : Polynomial k) ^ (Nat.card k) ^ (minpoly k ζ).natDegree - Polynomial.X :=
    ((minpoly.irreducible hζ).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X
      (n := (minpoly k ζ).natDegree)).mp dvd_rfl
  have hroot : Polynomial.aeval ζ
      ((Polynomial.X : Polynomial k) ^ (Nat.card k) ^ (minpoly k ζ).natDegree - Polynomial.X) = 0 :=
    (minpoly.dvd_iff).mp hdvd
  have hsub : ζ ^ ((Nat.card k) ^ (minpoly k ζ).natDegree) - ζ = 0 := by
    simpa only [map_sub, map_pow, Polynomial.aeval_X] using hroot
  have hpow : ζ ^ ((Nat.card k) ^ (minpoly k ζ).natDegree) = ζ := sub_eq_zero.mp hsub
  rwa [Nat.card_eq_fintype_card] at hpow

/-- **Frobenius fixes after `[k(ζ) : k]` steps** (the "`≤` half" of the degree identity).

For `k` a finite field, `K` a finite field with `k⟮ζ⟯ = K`, and `ζ` integral over `k`, the
`(minpoly k ζ).natDegree`-th iterate of `x ↦ x ^ #k` fixes `ζ`:
`ζ ^ (#k) ^ (minpoly k ζ).natDegree = ζ`.

Proof: `#K = (#k) ^ [K:k]` (`Module.card_eq_pow_finrank`) and `[K:k] = (minpoly k ζ).natDegree`
(`IntermediateField.adjoin.finrank`, using `k⟮ζ⟯ = K`), while every element `x` of a finite field
satisfies `x ^ #K = x` (`FiniteField.pow_card`).

Note (elaboration): `Module.card_eq_pow_finrank` must be applied with its type arguments fixed
(`(K := k) (V := K)`); otherwise instance search for `Fintype ?V` stalls on an undetermined
metavariable — the same failure mode as the `Fintype ↥(k⟮ζ⟯)` instance, which this statement avoids
by carrying `k⟮ζ⟯ = K` as a hypothesis instead of an intermediate field. -/
theorem pow_card_pow_natDegree_eq_self {k : Type*} [Field k] [Fintype k] {K : Type*} [Field K]
    [Algebra k K] [Fintype K] {ζ : K}
    (hgen : IntermediateField.adjoin k ({ζ} : Set K) = ⊤) (hζ : IsIntegral k ζ) :
    ζ ^ (Fintype.card k) ^ (minpoly k ζ).natDegree = ζ := by
  have hfin0 : Module.finrank k ↥(IntermediateField.adjoin k ({ζ} : Set K)) =
      (minpoly k ζ).natDegree := IntermediateField.adjoin.finrank hζ
  have hfin : Module.finrank k K = (minpoly k ζ).natDegree := by
    rw [hgen] at hfin0
    have htop : Module.finrank k ↥(⊤ : IntermediateField k K) = Module.finrank k K :=
      (IntermediateField.topEquiv (F := k) (E := K)).toLinearEquiv.finrank_eq
    rw [← htop]
    exact hfin0
  have hcard : Fintype.card K = (Fintype.card k) ^ (minpoly k ζ).natDegree := by
    rw [Module.card_eq_pow_finrank (K := k) (V := K), hfin]
  have hfix := FiniteField.pow_card ζ
  rw [hcard] at hfix
  exact hfix

/-- **Frobenius/degree lemma (finite fields).**  Let `k` be a finite field, `n > 0`, and let `ζ` be a
primitive `(#k ^ n - 1)`-th root of unity over `k`.  Then `ζ` has degree exactly `n` over `k`.

Equivalently: the Frobenius `x ↦ x ^ #k` acts on the group `μ_{#k^n - 1}` of order `#k^n - 1` as
`ζ ↦ ζ ^ #k` (`pow_sub_one_dvd_pow_sub_one_iff`), and for finite fields the degree of `ζ` over `k`
is exactly the order of that action.

This is the missing link for `f(q'|q) ≤ n` in `exists_galois_unramified_extension_of_inertiaDeg`:
for `L' = L(ζ_m)` with `m = q₀ ^ n - 1` and `q₀ = #(𝓞 L ⧸ q)`, the residue field `𝓞 L' ⧸ q'` is
generated over `𝓞 L ⧸ q` by the reduction of `ζ_m`, so
`f(q'|q) = [k(ζ̄_m) : k] = n`.

Proof plan (`sorry` for now):
* `ζ ^ (#k) ^ n = ζ`, because `ζ ^ (#k ^ n - 1) = 1` and `m = #k ^ n - 1`;
* if `ζ ^ (#k) ^ d = ζ` then `ζ ^ (#k ^ d - 1) = 1`, hence `(#k ^ n - 1) ∣ (#k ^ d - 1)` (as `ζ` has
  order exactly `#k ^ n - 1`), hence `n ∣ d` by `pow_sub_one_dvd_pow_sub_one_iff`;
* for finite fields, `[k(ζ) : k]` is the least `d` with `ζ ^ (#k) ^ d = ζ` (Frobenius fixed points
  of `𝔽_{q ^ d}`), and `[k(ζ) : k] = (minpoly k ζ).natDegree`. -/
theorem natDegree_minpoly_isPrimitiveRoot_card_pow_sub_one {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [Algebra k K] {n : ℕ} (hn : 0 < n) {ζ : K}
    (hζ : IsPrimitiveRoot ζ ((Fintype.card k) ^ n - 1)) :
    (minpoly k ζ).natDegree = n := by
  -- `ζ` is a root of the monic `X ^ (#k ^ n - 1) - 1`, hence integral over `k`
  have hm1 : 1 < (Fintype.card k) ^ n :=
    one_lt_pow₀ Fintype.one_lt_card (by omega : n ≠ 0)
  have hint : IsIntegral k ζ :=
    ⟨Polynomial.X ^ ((Fintype.card k) ^ n - 1) - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 (Nat.sub_pos_of_lt hm1).ne', by
        show Polynomial.aeval ζ ((Polynomial.X : Polynomial k) ^ ((Fintype.card k) ^ n - 1) - Polynomial.C (1 : k)) = 0
        simp [Polynomial.aeval_def, hζ.pow_eq_one]⟩
  -- the degree divides `n` (Frobenius has order exactly `n`), and `n` divides the degree
  refine Nat.dvd_antisymm ?_ ?_
  · exact natDegree_minpoly_dvd_of_pow_card_pow_eq_self hint
      (pow_card_pow_eq_self_of_isPrimitiveRoot hn hζ)
  · exact dvd_of_pow_card_pow_eq_self hn hζ
      (pow_card_pow_natDegree_eq_self_of_isIntegral hint)

end Commons.NumberTheory.NumberField.Completion

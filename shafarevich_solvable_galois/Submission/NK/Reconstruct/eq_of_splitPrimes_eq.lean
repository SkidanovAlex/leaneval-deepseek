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
import Submission.Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup_under_mul_card_ker
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.eq_one_of_fixes_sup
import Submission.NK.Reconstruct.restrictNormalHom_smul_valuationSubringAtPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The completely split primes determine a finite normal subextension

Let `K` be a number field, `K'/K` a Galois extension and `L, M ⊆ K'` finite normal intermediate
fields which are number fields.  If a prime `p` of `K` splits completely in `L` (that is, has a
prime of `𝓞 L` above it with ramification index and inertia degree both `1`) exactly when it
splits completely in `M`, then `L = M`.

The proof is the classical Čebotarev-density argument:

* the set of completely split primes has Dirichlet density `1 / [E : K]`
  (`hasDirichletDensity_primes_splitsCompletely`), so equal split-prime sets force equal degrees;
* a prime splitting completely in `L` and in `M` splits completely in the compositum `L ⊔ M`
  (the crux: the decomposition group of a prime of `L ⊔ M` over `p` restricts trivially to `L`
  and to `M`, hence is trivial, because an automorphism of the compositum fixing both factors is
  the identity);
* applying the density statement to `L ⊔ M` and to `L` gives `[L ⊔ M : K] = [L : K]`, whence
  `M ≤ L`, and symmetrically `L ≤ M`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.Reconstruct

open IsDedekindDomain

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

/-- The set of finite primes of `K` that split completely in the number field `E` over `K`: those
`p` having exactly `[E : K]` primes of `𝓞 E` above them. -/
def splitPrimesSet (K : Type*) [Field K] [NumberField K] (E : Type*) [Field E] [NumberField E]
    [Algebra K E] : Set (NK.Chebotarev.PrimeIdeal K) :=
  {p | (p.asIdeal.primesOver (NumberField.RingOfIntegers E)).ncard = Module.finrank K E}

/-- **Splitting completely, in the witness form, is the counting form.**  For a finite Galois
extension `E/K` of number fields, a prime `p` of `K` has a prime of `𝓞 E` above it with
ramification index and inertia degree one if and only if `p` has `[E : K]` primes above it. -/
theorem splitsCompletely_iff_ncard (K : Type*) [Field K] [NumberField K] (E : Type*) [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (p : NK.Chebotarev.PrimeIdeal K) :
    (∃ P : NK.Chebotarev.PrimeIdeal E, P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) ↔
      p ∈ splitPrimesSet K E := by
  show _ ↔ (p.asIdeal.primesOver (NumberField.RingOfIntegers E)).ncard = Module.finrank K E
  rw [Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
    (K := K) (L := E) p]
  constructor
  · rintro ⟨P, hP, he, hf⟩
    constructor
    · rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers E) p.asIdeal P.asIdeal (Gal(E/K)) (hp := hP)]
      exact he
    · rw [Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers E) p.asIdeal P.asIdeal (Gal(E/K)) (hp := hP)]
      exact hf
  · rintro ⟨he, hf⟩
    have hne : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers E)) :=
      Ideal.nonempty_primesOver p.asIdeal
    obtain ⟨P⟩ := hne
    have hP : (P : Ideal (NumberField.RingOfIntegers E)).LiesOver p.asIdeal := P.2.2
    refine ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot P.2⟩, hP, ?_, ?_⟩
    · rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers E) p.asIdeal P.1 (Gal(E/K)) (hPp := P.2.1) (hp := hP)]
      exact he
    · rw [← Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers E) p.asIdeal P.1 (Gal(E/K)) (hPp := P.2.1) (hp := hP)]
      exact hf

/-- The completely split primes have Dirichlet density the reciprocal of the degree. -/
theorem hasDirichletDensity_splitPrimesSet (K : Type*) [Field K] [NumberField K] (E : Type*)
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E] :
    NumberField.Set.HasDirichletDensity (splitPrimesSet K E)
      (1 / (Module.finrank K E : ℝ)) :=
  Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
    (K := K) (L := E)

/-- **A prime splitting completely in an extension splits completely in a subextension**: for a
tower `K ⊆ L ⊆ L ⊔ M` of number fields with `L ⊔ M` Galois over `K`, every prime of `K` splitting
completely in `L ⊔ M` splits completely in `L`.  This is the multiplicativity of ramification
index and inertia degree in towers. -/
theorem splitPrimesSet_sup_le {L M : IntermediateField K K'} [FiniteDimensional K L] [Normal K L]
    [NumberField ↥L] [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    [NumberField ↥(L ⊔ M)] :
    splitPrimesSet K ↥(L ⊔ M) ⊆ splitPrimesSet K ↥L := by
  letI : Algebra ↥L ↥(L ⊔ M) := (Subsemiring.inclusion (le_sup_left : L ≤ L ⊔ M)).toAlgebra
  haveI : IsScalarTower K ↥L ↥(L ⊔ M) := IsScalarTower.of_algebraMap_eq fun x => rfl
  intro p hp
  haveI hGalN : IsGalois K ↥(L ⊔ M) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalL : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  obtain ⟨heN, hfN⟩ :=
    (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := ↥(L ⊔ M)) p).mp hp
  have hne : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥(L ⊔ M))) :=
    Ideal.nonempty_primesOver p.asIdeal
  obtain ⟨R⟩ := hne
  set q : NK.Chebotarev.PrimeIdeal ↥(L ⊔ M) :=
    ⟨R.1, R.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot R.2⟩ with hq
  have hqLies : q.asIdeal.LiesOver p.asIdeal := R.2.2
  haveI hliesL : q.asIdeal.LiesOver (q.under (NumberField.RingOfIntegers ↥L)).asIdeal := ⟨rfl⟩
  -- the ramification index and inertia degree of `q` over `p` are one
  have heR : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers ↥(L ⊔ M)) p.asIdeal q.asIdeal (Gal(↥(L ⊔ M)/K))
      (hp := hqLies)]
    exact heN
  have hfR : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers ↥(L ⊔ M)) p.asIdeal q.asIdeal (Gal(↥(L ⊔ M)/K))
      (hp := hqLies)]
    exact hfN
  -- and hence so are those of the prime below on `L`
  have heLR : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.ramificationIdx
      (NumberField.RingOfIntegers K) = 1 := by
    have htw := Ideal.ramificationIdx_tower (R := NumberField.RingOfIntegers K)
      (S := NumberField.RingOfIntegers ↥L) (T := NumberField.RingOfIntegers ↥(L ⊔ M))
      (q.under (NumberField.RingOfIntegers ↥L)).asIdeal q.asIdeal
    have h1 : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers K) *
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L) = 1 := by
      rw [← htw]
      exact heR
    exact (mul_eq_one.mp h1).1
  have hfLR : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers K) = 1 := by
    have htw := Ideal.inertiaDeg_tower (R := NumberField.RingOfIntegers K)
      (S := NumberField.RingOfIntegers ↥L) (T := NumberField.RingOfIntegers ↥(L ⊔ M))
      (q.under (NumberField.RingOfIntegers ↥L)).asIdeal q.asIdeal
    have h1 : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ↥L) = 1 := by
      rw [← htw]
      exact hfR
    exact (mul_eq_one.mp h1).1
  have hLies : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    exact hqLies.over
  show (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard = Module.finrank K ↥L
  rw [Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
    (K := K) (L := ↥L) p]
  constructor
  · rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers ↥L) p.asIdeal
      (q.under (NumberField.RingOfIntegers ↥L)).asIdeal (Gal(↥L/K)) (hp := hLies)]
    exact heLR
  · rw [Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers ↥L) p.asIdeal
      (q.under (NumberField.RingOfIntegers ↥L)).asIdeal (Gal(↥L/K)) (hp := hLies)]
    exact hfLR

/-- **A prime splitting completely in two subextensions splits completely in their compositum.**
This is the crux of the reconstruction: for `p` splitting completely in `L` and in `M`, the
decomposition group of any prime of `𝓞 (L ⊔ M)` above `p` restricts trivially to `L` and to `M`,
hence is trivial, so `p` splits completely in `L ⊔ M`. -/
theorem splitPrimesSet_subset_sup {L M : IntermediateField K K'} [FiniteDimensional K L]
    [Normal K L] [NumberField ↥L] [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    [NumberField ↥(L ⊔ M)] {p : NK.Chebotarev.PrimeIdeal K}
    (hpL : p ∈ splitPrimesSet K ↥L) (hpM : p ∈ splitPrimesSet K ↥M) :
    p ∈ splitPrimesSet K ↥(L ⊔ M) := by
  letI : Algebra ↥L ↥(L ⊔ M) := (Subsemiring.inclusion (le_sup_left : L ≤ L ⊔ M)).toAlgebra
  haveI : IsScalarTower K ↥L ↥(L ⊔ M) := IsScalarTower.of_algebraMap_eq fun x => rfl
  letI : Algebra ↥M ↥(L ⊔ M) := (Subsemiring.inclusion (le_sup_right : M ≤ L ⊔ M)).toAlgebra
  haveI : IsScalarTower K ↥M ↥(L ⊔ M) := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI hGalL : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalM : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalN : IsGalois K ↥(L ⊔ M) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  obtain ⟨heL, hfL⟩ :=
    (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := ↥L) p).mp hpL
  obtain ⟨heM, hfM⟩ :=
    (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := ↥M) p).mp hpM
  have hne : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥(L ⊔ M))) :=
    Ideal.nonempty_primesOver p.asIdeal
  obtain ⟨R₀⟩ := hne
  set q : NK.Chebotarev.PrimeIdeal ↥(L ⊔ M) :=
    ⟨R₀.1, R₀.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot R₀.2⟩ with hq
  have hqLies : q.asIdeal.LiesOver p.asIdeal := R₀.2.2
  -- the decomposition group of `q` is trivial
  have hbot : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    have hσ' : σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥(L ⊔ M) q =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥(L ⊔ M) q :=
      (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
        q σ).mpr hσ
    -- restriction to `L` is trivial
    have hL1 : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥L σ = 1 := by
      have hkey := restrictNormalHom_smul_valuationSubringAtPrime (K := K) (E := ↥L)
        (N := ↥(L ⊔ M)) (q := q) (q' := q.under (NumberField.RingOfIntegers ↥L)) rfl hσ'
      have hmem : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥L σ ∈
          Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
            (q.under (NumberField.RingOfIntegers ↥L)) :=
        (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
          (q.under (NumberField.RingOfIntegers ↥L)) _).mp hkey
      have hLiesP : (q.under (NumberField.RingOfIntegers ↥L)).asIdeal.LiesOver p.asIdeal := by
        refine ⟨?_⟩
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
        exact hqLies.over
      have hbotP : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
          (q.under (NumberField.RingOfIntegers ↥L)) = ⊥ :=
        (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
          p _ hLiesP).mpr ⟨heL, hfL⟩
      rw [hbotP] at hmem
      exact Subgroup.mem_bot.mp hmem
    -- restriction to `M` is trivial
    have hM1 : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥M σ = 1 := by
      have hkey := restrictNormalHom_smul_valuationSubringAtPrime (K := K) (E := ↥M)
        (N := ↥(L ⊔ M)) (q := q) (q' := q.under (NumberField.RingOfIntegers ↥M)) rfl hσ'
      have hmem : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L ⊔ M)) ↥M σ ∈
          Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
            (q.under (NumberField.RingOfIntegers ↥M)) :=
        (Commons.NumberTheory.NumberField.Completion.smul_valuationSubringAtPrime_eq_iff_mem_decompositionSubgroup
          (q.under (NumberField.RingOfIntegers ↥M)) _).mp hkey
      have hLiesQ : (q.under (NumberField.RingOfIntegers ↥M)).asIdeal.LiesOver p.asIdeal := by
        refine ⟨?_⟩
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
        exact hqLies.over
      have hbotQ : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K)
          (q.under (NumberField.RingOfIntegers ↥M)) = ⊥ :=
        (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
          p _ hLiesQ).mpr ⟨heM, hfM⟩
      rw [hbotQ] at hmem
      exact Subgroup.mem_bot.mp hmem
    -- an automorphism of the compositum fixing both factors is the identity
    refine eq_one_of_fixes_sup L M σ ?_ ?_
    · intro x
      have h3 : (σ.restrictNormal ↥L) x = x := by
        rw [show (σ.restrictNormal ↥L) = 1 from hL1]
        rfl
      have h2 := AlgEquiv.restrictNormal_commutes (F := K) σ ↥L x
      rw [h3] at h2
      have h4 : algebraMap ↥L ↥(L ⊔ M) x =
          ⟨x.1, (le_sup_left : L ≤ L ⊔ M) x.2⟩ := Subtype.ext rfl
      rw [h4] at h2
      exact h2.symm
    · intro x
      have h3 : (σ.restrictNormal ↥M) x = x := by
        rw [show (σ.restrictNormal ↥M) = 1 from hM1]
        rfl
      have h2 := AlgEquiv.restrictNormal_commutes (F := K) σ ↥M x
      rw [h3] at h2
      have h4 : algebraMap ↥M ↥(L ⊔ M) x =
          ⟨x.1, (le_sup_right : M ≤ L ⊔ M) x.2⟩ := Subtype.ext rfl
      rw [h4] at h2
      exact h2.symm
  -- hence the local degree of `q` is one, and `p` splits completely in `L ⊔ M`
  have hcard : Nat.card (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
      (K := K) q) = 1 := (Subgroup.eq_bot_iff_card _).mp hbot
  have hcard' := Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup
    (K := K) (L := ↥(L ⊔ M)) p q hqLies
  rw [hcard] at hcard'
  obtain ⟨heN, hfN⟩ := mul_eq_one.mp hcard'.symm
  exact (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
    (K := K) (L := ↥(L ⊔ M)) p).mpr ⟨heN, hfN⟩

/-- **Two finite normal number-field subextensions with the same completely split primes are
equal.**  This is the classical statement that the completely split primes determine a finite
normal subextension, used to identify the level correspondence attached to an isomorphism of
absolute Galois groups. -/
theorem eq_of_splitPrimes_eq {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsGalois K K'] {L M : IntermediateField K K'} [FiniteDimensional K L] [Normal K L]
    [NumberField ↥L] [FiniteDimensional K M] [Normal K M] [NumberField ↥M]
    (h : ∀ p : NK.Chebotarev.PrimeIdeal K,
      (∃ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver p.asIdeal ∧
          P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
          P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) ↔
        (∃ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver p.asIdeal ∧
          Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
          Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1)) :
    L = M := by
  haveI hGalL : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hGalM : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI : NumberField ↥(L ⊔ M) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (L ⊔ M)
  haveI hGalN : IsGalois K ↥(L ⊔ M) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- the split prime sets of `L` and `M` agree
  have hset : splitPrimesSet K ↥L = splitPrimesSet K ↥M := by
    ext p
    rw [← splitsCompletely_iff_ncard K ↥L p, ← splitsCompletely_iff_ncard K ↥M p]
    exact h p
  -- and both agree with the split prime set of the compositum
  have hsupL : splitPrimesSet K ↥(L ⊔ M) = splitPrimesSet K ↥L := by
    refine Set.Subset.antisymm (splitPrimesSet_sup_le (L := L) (M := M)) ?_
    intro p hp
    exact splitPrimesSet_subset_sup (L := L) (M := M) hp (hset ▸ hp)
  have hsupM : splitPrimesSet K ↥(L ⊔ M) = splitPrimesSet K ↥M := by
    rw [hsupL, hset]
  -- densities
  have hdL : NumberField.Set.HasDirichletDensity (splitPrimesSet K ↥L)
      (1 / (Module.finrank K ↥L : ℝ)) := hasDirichletDensity_splitPrimesSet K ↥L
  have hdM : NumberField.Set.HasDirichletDensity (splitPrimesSet K ↥M)
      (1 / (Module.finrank K ↥M : ℝ)) := hasDirichletDensity_splitPrimesSet K ↥M
  have hdN : NumberField.Set.HasDirichletDensity (splitPrimesSet K ↥(L ⊔ M))
      (1 / (Module.finrank K ↥(L ⊔ M) : ℝ)) := hasDirichletDensity_splitPrimesSet K ↥(L ⊔ M)
  have hdNL : NumberField.Set.HasDirichletDensity (splitPrimesSet K ↥L)
      (1 / (Module.finrank K ↥(L ⊔ M) : ℝ)) := hsupL ▸ hdN
  have hdNM : NumberField.Set.HasDirichletDensity (splitPrimesSet K ↥M)
      (1 / (Module.finrank K ↥(L ⊔ M) : ℝ)) := hsupM ▸ hdN
  have hdegL : Module.finrank K ↥L = Module.finrank K ↥(L ⊔ M) := by
    have heq := tendsto_nhds_unique hdL hdNL
    rw [one_div, one_div] at heq
    have h2 : (Module.finrank K ↥L : ℝ) = (Module.finrank K ↥(L ⊔ M) : ℝ) := inv_inj.mp heq
    exact_mod_cast h2
  have hdegM : Module.finrank K ↥M = Module.finrank K ↥(L ⊔ M) := by
    have heq := tendsto_nhds_unique hdM hdNM
    rw [one_div, one_div] at heq
    have h2 : (Module.finrank K ↥M : ℝ) = (Module.finrank K ↥(L ⊔ M) : ℝ) := inv_inj.mp heq
    exact_mod_cast h2
  have hLtop : L = L ⊔ M := IntermediateField.eq_of_le_of_finrank_eq le_sup_left hdegL
  have hMtop : M = L ⊔ M := IntermediateField.eq_of_le_of_finrank_eq le_sup_right hdegM
  have hMleL : M ≤ L := by rw [hLtop]; exact le_sup_right
  have hLleM : L ≤ M := by rw [hMtop]; exact le_sup_left
  exact le_antisymm hLleM hMleL

end NK.Reconstruct

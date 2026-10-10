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
import Submission.NK.ReconstructField.conjRingEquiv_eq_levelMapEquiv_of_primeTransport_eq
import Submission.NK.ReconstructField.exists_restrict_of_levelIso
import Submission.NK.ReconstructField.finrank_tower_eq_of_ringEquiv
import Submission.NK.ReconstructField.localDeg_primeTransport_nested
import Submission.NK.ReconstructField.ncard_primesOver_levelPrimeMapGen
import Submission.NK.ReconstructField.primeBelowNat_levelPrimeMap
import Submission.NK.ReconstructField.sum_localDeg_primesOver
import Submission.NK.UchidaKummer.Kummer.machinery_of_isPrimitiveRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.ReconstructField

open NK.Reconstruct

/-! ## Helper lemmas proved in this file -/

/-- The rational prime below a finite prime is determined by `primeBelowNat`. -/
lemma primeBelow_eq_of_primeBelowNat_eq {K : Type*} [Field K] [NumberField K]
    {P Q : NK.Chebotarev.PrimeIdeal K}
    (h : NK.LocalInputs.primeBelowNat K P = NK.LocalInputs.primeBelowNat K Q) :
    NK.LocalInputs.primeBelow K P = NK.LocalInputs.primeBelow K Q := by
  have h2 : Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow K P) =
      Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow K Q) :=
    Subtype.ext h
  exact Rat.HeightOneSpectrum.primesEquiv.injective h2

/-- **The contraction of a transported prime**: for compatible isomorphisms of two extensions of
number fields, the transport of primes commutes with the contraction to the base fields. -/
lemma under_primeTransport {L₁ L₂ M₁ M₂ : Type*} [Field L₁] [NumberField L₁] [Field L₂]
    [NumberField L₂] [Field M₁] [NumberField M₁] [Field M₂] [NumberField M₂]
    [Algebra L₁ L₂] [Algebra M₁ M₂] (σ : L₂ ≃+* M₂) (τ : L₁ ≃+* M₁)
    (hσ : ∀ x : L₁, σ (algebraMap L₁ L₂ x) = algebraMap M₁ M₂ (τ x))
    (Q : NK.Chebotarev.PrimeIdeal M₂) (P : NK.Chebotarev.PrimeIdeal M₁)
    (hQ : Q.asIdeal.under (NumberField.RingOfIntegers M₁) = P.asIdeal) :
    (NK.Reconstruct.primeTransport σ.symm Q).asIdeal.under (NumberField.RingOfIntegers L₁) =
      (NK.Reconstruct.primeTransport τ.symm P).asIdeal := by
  rw [NK.ReconstructField.primeTransport_asIdeal σ.symm Q,
    NK.ReconstructField.primeTransport_asIdeal τ.symm P]
  have hμ : ∀ x : M₁, σ.symm (algebraMap M₁ M₂ x) = algebraMap L₁ L₂ (τ.symm x) := by
    intro x
    apply σ.injective
    rw [σ.apply_symm_apply, hσ (τ.symm x), τ.apply_symm_apply]
  have hφ := NK.ReconstructField.ringOfIntegersEquiv_algebraMap σ.symm τ.symm hμ
  have hcomp := NK.ReconstructField.comap_map_eq_map_comap
      (NK.Reconstruct.ringOfIntegersEquiv σ.symm)
      (NK.Reconstruct.ringOfIntegersEquiv τ.symm)
      (algebraMap (NumberField.RingOfIntegers M₁) (NumberField.RingOfIntegers M₂))
      (algebraMap (NumberField.RingOfIntegers L₁) (NumberField.RingOfIntegers L₂)) hφ Q.asIdeal
  rw [Ideal.under_def] at hQ ⊢
  rw [← hQ]
  exact hcomp

/-- Arithmetic: `ℓ ^ a * N = ℓ ^ b * N` with `N ≠ 0` and `ℓ ≥ 2` forces `a = b`. -/
lemma pow_eq_of_mul_eq_mul {ℓ a b N : ℕ} (hℓ : 2 ≤ ℓ) (hN : N ≠ 0)
    (h : ℓ ^ a * N = ℓ ^ b * N) : a = b :=
  Nat.pow_right_injective hℓ (Nat.mul_right_cancel (Nat.pos_of_ne_zero hN) h)

/-- **The contraction to `𝓞 ℚ` of a pushed-forward ideal is unchanged**: the induced ring
isomorphism of rings of integers of two number fields is the identity on the images of `𝓞 ℚ`. -/
lemma under_map_ringOfIntegersEquiv_rat {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (e : A ≃+* B) (I : Ideal (NumberField.RingOfIntegers A)) :
    Ideal.under (NumberField.RingOfIntegers ℚ)
        (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e) I) =
      Ideal.under (NumberField.RingOfIntegers ℚ) I := by
  rw [Ideal.under_def, Ideal.under_def]
  have hrefl : NK.Reconstruct.ringOfIntegersEquiv (RingEquiv.refl ℚ) =
      (RingEquiv.refl (NumberField.RingOfIntegers ℚ)) := by
    ext x
    rw [NK.Reconstruct.ringOfIntegersEquiv_apply]
    rfl
  have hφ : ∀ x : NumberField.RingOfIntegers ℚ,
      (NK.Reconstruct.ringOfIntegersEquiv e)
          (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers A) x) =
        algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers B)
          ((NK.Reconstruct.ringOfIntegersEquiv (RingEquiv.refl ℚ)) x) := by
    intro x
    rw [hrefl]
    exact NK.ReconstructField.ringOfIntegersEquiv_algebraMap e (RingEquiv.refl ℚ)
      (fun q => RingHom.map_rat_algebraMap (e : A →+* B) q) x
  have hcomp := NK.ReconstructField.comap_map_eq_map_comap
    (NK.Reconstruct.ringOfIntegersEquiv e)
    (NK.Reconstruct.ringOfIntegersEquiv (RingEquiv.refl ℚ))
    (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers A))
    (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers B)) hφ I
  rw [hcomp, hrefl]
  exact Ideal.map_id _

/-- **The rational prime below a transported prime is unchanged.** -/
lemma primeBelowNat_primeTransport {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (e : A ≃+* B) (P : NK.Chebotarev.PrimeIdeal A) :
    NK.LocalInputs.primeBelowNat B (NK.Reconstruct.primeTransport e P) =
      NK.LocalInputs.primeBelowNat A P := by
  have h : NK.LocalInputs.primeBelow B (NK.Reconstruct.primeTransport e P) =
      NK.LocalInputs.primeBelow A P := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    show Ideal.under (NumberField.RingOfIntegers ℚ)
        (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv e) P.asIdeal) =
      Ideal.under (NumberField.RingOfIntegers ℚ) P.asIdeal
    exact under_map_ringOfIntegersEquiv_rat e P.asIdeal
  rw [NK.LocalInputs.primeBelowNat, NK.LocalInputs.primeBelowNat, h]

/-- `ncard` of a finite set is the cardinality of its type. -/
lemma ncard_eq_fintypeCard {α : Type*} (s : Set α) [Fintype s] : s.ncard = Fintype.card s := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- The sum of a constant over the fibre of primes above `P`, in terms of `ncard`. -/
lemma sum_localDeg_eq_card_mul {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (P : NK.Chebotarev.PrimeIdeal K) (c : ℕ)
    (h : ∀ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg
        ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P = c) :
    ∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg
        ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P =
      c * (P.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard := by
  have h₁ : (∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg
        ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P) =
      ∑ _Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L), c :=
    Finset.sum_congr rfl (fun Q _ => h Q)
  rw [h₁, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  exact congrArg (fun n => c * n) (ncard_eq_fintypeCard _).symm

/-! ## Temporary copies of the lemmas delegated to the fleet -/







/-! ## The main theorem -/

/-- **The finite prime-matching step of the reconstruction** (the differentiation/pinning step of
Neukirch's Lemma *`α identifies with σ on primes`*, CoNF XII §12.2): for every finite set `S` of
primes of a finite normal level `L` there is a level isomorphism `τ : ↥L ≃+* ↥(levelMap ϕ L)` whose
induced map on primes agrees with the local correspondence `levelPrimeMap ϕ hϕ a L` on `S`. -/
theorem key_finite_prime_match {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ℓ : ℕ}
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L)]
    (S : Finset (NK.Chebotarev.PrimeIdeal ↥L)) :
    ∃ τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L),
      ∀ P ∈ S, NK.Reconstruct.primeTransport τ P =
        NK.ReconstructField.levelPrimeMap ϕ hϕ a L P := by
  classical
  -- ## Step 1: the finite set `R'` of primes of `L` over the rational primes below `S`
  let R' : Finset (NK.Chebotarev.PrimeIdeal ↥L) :=
    S.biUnion (fun P => NK.UchidaKummer.Differentiation.primesOverFinset (K := ℚ) (L := ↥L)
      (NK.LocalInputs.primeBelow ↥L P))
  have hSR' : ∀ P ∈ S, P ∈ R' := by
    intro P hP
    refine Finset.mem_biUnion.mpr ⟨P, hP, ?_⟩
    rw [NK.UchidaKummer.Differentiation.mem_primesOverFinset]
    exact NK.LocalInputs.primeBelow_liesOver ↥L P
  have hR'cl : ∀ Q : NK.Chebotarev.PrimeIdeal ↥L,
      NK.LocalInputs.primeBelowNat ↥L Q ∈ S.image (NK.LocalInputs.primeBelowNat ↥L) →
        Q ∈ R' := by
    intro Q hQ
    obtain ⟨P, hP, hPQ⟩ := Finset.mem_image.mp hQ
    refine Finset.mem_biUnion.mpr ⟨P, hP, ?_⟩
    rw [NK.UchidaKummer.Differentiation.mem_primesOverFinset]
    have h1 : NK.LocalInputs.primeBelow ↥L Q = NK.LocalInputs.primeBelow ↥L P :=
      primeBelow_eq_of_primeBelowNat_eq hPQ.symm
    rw [← h1]
    exact NK.LocalInputs.primeBelow_liesOver ↥L Q
  -- ## Step 2: enumeration of `R'` and the exponent function
  let idx : (P : NK.Chebotarev.PrimeIdeal ↥L) → P ∈ R' → Fin R'.card :=
    fun P hP => Finset.equivFin R' ⟨P, hP⟩
  let 𝔭 : Fin R'.card → NK.Chebotarev.PrimeIdeal ↥L :=
    fun i => (((Finset.equivFin R').symm i : ↥R') : NK.Chebotarev.PrimeIdeal ↥L)
  have h𝔭idx : ∀ (P : NK.Chebotarev.PrimeIdeal ↥L) (hP : P ∈ R'), 𝔭 (idx P hP) = P := by
    intro P hP
    show (((Finset.equivFin R').symm (Finset.equivFin R' ⟨P, hP⟩) : ↥R') :
      NK.Chebotarev.PrimeIdeal ↥L) = P
    rw [Equiv.symm_apply_apply]
  have h𝔭inj : Function.Injective 𝔭 := by
    intro i j hij
    have h1 : ((Finset.equivFin R').symm i : ↥R') = (Finset.equivFin R').symm j := Subtype.ext hij
    exact (Finset.equivFin R').symm.injective h1
  let aexp : Fin R'.card → ℕ := fun i => (i : ℕ) + 1
  have haexpinj : Function.Injective aexp := by
    intro i j h
    exact Fin.ext (Nat.succ.inj h)
  -- ## Step 3: the differentiation over the base field `↥L`
  have hμL : ∃ ζ : ↥L, IsPrimitiveRoot ζ ℓ := by
    obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨algebraMap K₁ ↥L ζ, hζ.map_of_injective (RingHom.injective _)⟩
  haveI hSepL : IsSepClosure ↥L K₁' := NK.Reconstruct.isSepClosure_level L
  have hDiff : NK.UchidaKummer.IsDifferentiable ↥L K₁' ℓ :=
    NK.UchidaKummer.isDifferentiable_of_exists_isPrimitiveRoot (K := ↥L) (K' := K₁') ℓ hℓ hμL
  obtain ⟨E₀, hE₀fd, hE₀nf, hE₀deg⟩ := hDiff R'.card 𝔭 h𝔭inj aexp
  haveI hE₀fdI : FiniteDimensional ↥L E₀ := hE₀fd
  haveI hE₀nfI : NumberField ↥E₀ := hE₀nf
  -- ## Step 4: `E` as a level over `K₁`, the isomorphism `σ` and its restriction `τ`
  let E : IntermediateField K₁ K₁' := IntermediateField.restrictScalars K₁ E₀
  have hLE : L ≤ E := by
    intro x hx
    show x ∈ E₀
    exact (bot_le : (⊥ : IntermediateField ↥L K₁') ≤ E₀)
      (IntermediateField.mem_bot.mpr ⟨⟨x, hx⟩, rfl⟩)
  letI hAlgL : Algebra ↥L ↥E := (inferInstance : Algebra ↥L ↥E₀)
  haveI hTowerL : IsScalarTower K₁ ↥L ↥E := (inferInstance : IsScalarTower K₁ ↥L ↥E₀)
  haveI hfdLE : FiniteDimensional ↥L ↥E := (inferInstance : FiniteDimensional ↥L ↥E₀)
  haveI hfdE : FiniteDimensional K₁ E := FiniteDimensional.trans K₁ ↥L ↥E
  haveI hnfE : NumberField ↥E := (inferInstance : NumberField ↥E₀)
  have hincl₁ : ∀ x : ↥L, (algebraMap ↥L ↥E) x = ⟨(x : K₁'), hLE x.2⟩ := fun x => Subtype.ext rfl
  obtain ⟨σ⟩ := hlev E
  obtain ⟨τ, hτ⟩ := exists_restrict_of_levelIso ϕ hϕ L E hLE σ ⟨(hlev L).some⟩
  -- ## Step 5: the corresponding level `E₂` and its base `M'`
  let M' : IntermediateField K₂ K₂' := NK.Reconstruct.levelMap ϕ L
  let E₂ : IntermediateField K₂ K₂' := NK.Reconstruct.levelMap ϕ E
  have hmono : M' ≤ E₂ := NK.Reconstruct.levelMap_mono ϕ hLE
  haveI hnfE₂ : NumberField ↥E₂ := by
    have h := NK.Reconstruct.numberField_levelMap hϕ E
    exact h
  haveI hfdE₂ : FiniteDimensional K₂ E₂ := (inferInstance : FiniteDimensional K₂ ↥(NK.Reconstruct.levelMap ϕ E))
  haveI hfdM' : FiniteDimensional K₂ M' := (inferInstance : FiniteDimensional K₂ ↥(NK.Reconstruct.levelMap ϕ L))
  haveI hnfM' : NumberField ↥M' := (inferInstance : NumberField ↥(NK.Reconstruct.levelMap ϕ L))
  let gi : ↥M' →ₐ[K₂] ↥E₂ := IntermediateField.inclusion hmono
  letI hAlgM : Algebra ↥M' ↥E₂ := gi.toRingHom.toAlgebra
  haveI hTowerM : IsScalarTower K₂ ↥M' ↥E₂ := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    exact Subtype.ext rfl
  haveI hfdME : FiniteDimensional ↥M' ↥E₂ :=
    Module.Finite.of_restrictScalars_finite K₂ ↥M' ↥E₂
  have hincl₂ : ∀ y : ↥M', (algebraMap ↥M' ↥E₂) y = ⟨(y : K₂'), hmono y.2⟩ :=
    fun y => Subtype.ext rfl
  -- ## Step 6: the counting lemma and the two fibre sums
  have hcount : ∀ P : NK.Chebotarev.PrimeIdeal ↥L,
      (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard =
        ((NK.ReconstructField.levelPrimeMap ϕ hϕ a L P).asIdeal.primesOver
          (NumberField.RingOfIntegers ↥E₂)).ncard := fun P =>
    ncard_primesOver_levelPrimeMapGen ϕ hϕ a L E hLE hincl₁ hincl₂ P
  have hsumL : ∀ P : NK.Chebotarev.PrimeIdeal ↥L,
      (∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E),
        NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P) =
      Module.finrank ↥L ↥E := fun P => sum_localDeg_primesOver P
  have hsumR : ∀ Q₀ : NK.Chebotarev.PrimeIdeal ↥M',
      (∑ Q : Q₀.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂),
        NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver Q₀.ne_bot Q.2⟩ Q₀) =
      Module.finrank ↥M' ↥E₂ := fun Q₀ => sum_localDeg_primesOver Q₀
  have hτσ : ∀ x : ↥L, σ (algebraMap ↥L ↥E x) = algebraMap ↥M' ↥E₂ (τ x) := by
    intro x
    rw [hincl₁ x, hincl₂ (τ x)]
    exact Subtype.ext (hτ x).symm
  have hfin : Module.finrank ↥L ↥E = Module.finrank ↥M' ↥E₂ :=
    finrank_tower_eq_of_ringEquiv (K := K₁) (L := ↥L) (E := ↥E) (K' := K₂) (L' := ↥M')
      (E' := ↥E₂) σ τ hτσ
  -- ## Step 7: the pinning
  have hmatch : ∀ P ∈ S, NK.Reconstruct.primeTransport τ P =
      NK.ReconstructField.levelPrimeMap ϕ hϕ a L P := by
    intro P hP
    have hPR' : P ∈ R' := hSR' P hP
    set αP : NK.Chebotarev.PrimeIdeal ↥M' :=
      NK.ReconstructField.levelPrimeMap ϕ hϕ a L P with hαP
    set Pt : NK.Chebotarev.PrimeIdeal ↥L := NK.Reconstruct.primeTransport τ.symm αP with hPt
    have hτPt : NK.Reconstruct.primeTransport τ Pt = αP := by
      rw [hPt]
      exact NK.ReconstructField.primeTransport_symm_apply τ αP
    have hPtR' : Pt ∈ R' := by
      refine hR'cl Pt ?_
      rw [hPt, primeBelowNat_primeTransport τ.symm αP, hαP,
        primeBelowNat_levelPrimeMap ϕ hϕ a L P]
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
    have hdegP : ∀ Q : NK.Chebotarev.PrimeIdeal ↥E, Q.asIdeal.LiesOver P.asIdeal →
        NK.UchidaKummer.localDeg Q P = ℓ ^ (aexp (idx P hPR')) := by
      intro Q hQ
      have h := hE₀deg (idx P hPR') Q (by rw [h𝔭idx]; exact hQ)
      rwa [h𝔭idx] at h
    have hdegPt : ∀ Q : NK.Chebotarev.PrimeIdeal ↥E, Q.asIdeal.LiesOver Pt.asIdeal →
        NK.UchidaKummer.localDeg Q Pt = ℓ ^ (aexp (idx Pt hPtR')) := by
      intro Q hQ
      have h := hE₀deg (idx Pt hPtR') Q (by rw [h𝔭idx]; exact hQ)
      rwa [h𝔭idx] at h
    have hdegE₂ : ∀ Q' : αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂),
        NK.UchidaKummer.localDeg
          ⟨Q'.1, Q'.2.1, Ideal.ne_bot_of_mem_primesOver αP.ne_bot Q'.2⟩ αP =
        ℓ ^ (aexp (idx Pt hPtR')) := by
      intro Q'
      set Q'' : NK.Chebotarev.PrimeIdeal ↥E :=
        NK.Reconstruct.primeTransport σ.symm
          ⟨Q'.1, Q'.2.1, Ideal.ne_bot_of_mem_primesOver αP.ne_bot Q'.2⟩ with hQ''def
      have hQ''over : Q''.asIdeal.LiesOver Pt.asIdeal := by
        have h := under_primeTransport σ τ hτσ
          (⟨Q'.1, Q'.2.1, Ideal.ne_bot_of_mem_primesOver αP.ne_bot Q'.2⟩ :
            NK.Chebotarev.PrimeIdeal ↥E₂) αP Q'.2.2.over.symm
        rw [← hPt] at h
        rw [hQ''def]
        exact Ideal.LiesOver.mk h.symm
      have h1 : NK.UchidaKummer.localDeg Q'' Pt = ℓ ^ (aexp (idx Pt hPtR')) :=
        hdegPt Q'' hQ''over
      have h2 : NK.UchidaKummer.localDeg (NK.Reconstruct.primeTransport σ Q'')
          (NK.Reconstruct.primeTransport τ Pt) = NK.UchidaKummer.localDeg Q'' Pt :=
        localDeg_primeTransport_nested σ τ hτσ Q'' Pt hQ''over
      rw [hτPt] at h2
      rw [← h1, ← h2]
      congr 1
      rw [hQ''def, NK.ReconstructField.primeTransport_symm_apply]
    have hP'sum : (∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E),
        NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P) =
        ℓ ^ (aexp (idx P hPR')) * (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard :=
      sum_localDeg_eq_card_mul P _ (fun Q => hdegP ⟨Q.1, Q.2.1,
        Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ Q.2.2)
    have hα'sum : (∑ Q : αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂),
        NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver αP.ne_bot Q.2⟩ αP) =
        ℓ ^ (aexp (idx Pt hPtR')) *
          (αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂)).ncard :=
      sum_localDeg_eq_card_mul αP _ (fun Q => hdegE₂ Q)
    have hcount' : (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard =
        (αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂)).ncard := by
      rw [hαP]
      exact hcount P
    have hkey : ℓ ^ (aexp (idx P hPR')) * (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard =
        ℓ ^ (aexp (idx Pt hPtR')) *
          (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard := by
      calc ℓ ^ (aexp (idx P hPR')) * (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard
          = ∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E),
              NK.UchidaKummer.localDeg
                ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P := hP'sum.symm
        _ = Module.finrank ↥L ↥E := hsumL P
        _ = Module.finrank ↥M' ↥E₂ := hfin
        _ = ∑ Q : αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂),
              NK.UchidaKummer.localDeg
                ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver αP.ne_bot Q.2⟩ αP := (hsumR αP).symm
        _ = ℓ ^ (aexp (idx Pt hPtR')) *
              (αP.asIdeal.primesOver (NumberField.RingOfIntegers ↥E₂)).ncard := hα'sum
        _ = ℓ ^ (aexp (idx Pt hPtR')) *
              (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard := by rw [hcount']
    have hNpos : (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard ≠ 0 := by
      intro h0
      have hpos : 0 < ℓ ^ (aexp (idx P hPR')) *
          (P.asIdeal.primesOver (NumberField.RingOfIntegers ↥E)).ncard := by
        rw [← hP'sum, hsumL P]
        exact Module.finrank_pos
      rw [h0, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    have ha : aexp (idx P hPR') = aexp (idx Pt hPtR') :=
      pow_eq_of_mul_eq_mul hℓ.two_le hNpos hkey
    have hidx : idx P hPR' = idx Pt hPtR' := haexpinj ha
    have hPeq : P = Pt := by
      rw [← h𝔭idx P hPR', ← h𝔭idx Pt hPtR', hidx]
    rw [hPeq, hτPt, hαP]
  -- ## Step 8: conclude
  exact ⟨τ, hmatch⟩

end NK.ReconstructField

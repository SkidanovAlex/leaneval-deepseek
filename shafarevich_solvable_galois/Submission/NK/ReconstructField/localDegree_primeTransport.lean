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
import Submission.NK.Reconstruct.Transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local degree `e · f` is invariant under an isomorphism of number field extensions

Let `A₁ → B₁` and `A₂ → B₂` be extensions of number fields, and let `μ : B₁ ≃+* B₂` be a field
isomorphism which is compatible with a field isomorphism `μ₀ : A₁ ≃+* A₂` of the base fields,
`μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x)`.  Then `μ` induces a ring isomorphism
`𝓞 B₁ ≃+* 𝓞 B₂` of the rings of integers which is compatible, in turn, with the induced
isomorphism `𝓞 A₁ ≃+* 𝓞 A₂` of the rings of integers of the base fields.

Hence the whole arithmetic of the extension `B₁/A₁` transports to `B₂/A₂`: for a prime `P` of
`𝓞 B₁`, the corresponding prime `primeTransport μ P = μ(P)` of `𝓞 B₂` has the same ramification
index and the same inertia degree over the base field.  Consequently the *local degree*
`e(P) · f(P)` — the degree of the local extension at `P` — is preserved:

`P.ramificationIdx (𝓞 A₁) * P.inertiaDeg (𝓞 A₁)
   = (primeTransport μ P).ramificationIdx (𝓞 A₂) * (primeTransport μ P).inertiaDeg (𝓞 A₂)`.

The proof is a transport of the definitions:
* the ramification index is the multiplicity of `P` in the extension of the prime below it
  (`Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity`), and multiplicity is invariant under a
  ring equivalence of the ideal monoids (`multiplicity_map_eq`);
* the inertia degree is the degree of the residue field extension
  (`Ideal.inertiaDeg_eq_of_isMaximal`), and the residue field extension is transported by the
  induced isomorphism of quotients (`Ideal.quotientEquiv`), whence the degrees agree
  (`Algebra.finrank_eq_of_equiv_equiv`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace NK.ReconstructField

section Abstract

variable {R₁ R₂ S₁ S₂ : Type*} [CommRing R₁] [CommRing R₂] [CommRing S₁] [CommRing S₂]

/-- **The prime below the image is the image of the prime below.**

Let `f₁ : R₁ →+* S₁`, `f₂ : R₂ →+* S₂` be two ring homomorphisms, let `φ : S₁ ≃+* S₂` and
`φ₀ : R₁ ≃+* R₂` be ring equivalences commuting with them, `φ (f₁ x) = f₂ (φ₀ x)`.  Then for every
ideal `q` of `S₁`, the contraction of the image `φ q` along `f₂` is the image under `φ₀` of the
contraction of `q` along `f₁`. -/
lemma comap_map_eq_map_comap (φ : S₁ ≃+* S₂) (φ₀ : R₁ ≃+* R₂) (f₁ : R₁ →+* S₁)
    (f₂ : R₂ →+* S₂) (hφ : ∀ x : R₁, φ (f₁ x) = f₂ (φ₀ x)) (q : Ideal S₁) :
    Ideal.comap f₂ (Ideal.map φ q) = Ideal.map φ₀ (Ideal.comap f₁ q) := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap, Ideal.mem_map_of_equiv φ] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Ideal.mem_map_of_equiv φ₀]
    refine ⟨φ₀.symm x, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      have hxy : f₁ (φ₀.symm x) = y := by
        apply φ.injective
        rw [hφ, φ₀.apply_symm_apply]
        exact hyx.symm
      rw [hxy]
      exact hy
    · simp
  · intro x hx
    rw [Ideal.mem_map_of_equiv φ₀] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [Ideal.mem_comap, ← hφ z]
    exact Ideal.mem_map_of_mem φ (Ideal.mem_comap.mp hz)

/-- **The ring equivalence of ideal monoids induced by a ring equivalence.**

The map `Ideal.map e` is a bijection on ideals, hence a ring equivalence of the (multiplicative)
monoids of ideals.  It is used to transport multiplicities, hence ramification indices. -/
noncomputable def idealMapRingEquiv (e : R₁ ≃+* R₂) : Ideal R₁ ≃+* Ideal R₂ :=
  RingEquiv.ofBijective (Ideal.mapHom e) (by
    have hleft : ∀ K : Ideal R₁,
        Ideal.map (e.symm : R₂ →+* R₁) ((Ideal.mapHom e) K) = K := by
      intro K
      rw [Ideal.mapHom_apply]
      change Ideal.map (e.symm : R₂ →+* R₁) (Ideal.map (e : R₁ →+* R₂) K) = K
      rw [Ideal.map_map,
        show (e.symm : R₂ →+* R₁).comp (e : R₁ →+* R₂) = RingHom.id R₁ from
          RingHom.ext fun x => e.symm_apply_apply x,
        Ideal.map_id]
    have hright : ∀ K : Ideal R₂,
        Ideal.map (e : R₁ →+* R₂) ((Ideal.mapHom e.symm) K) = K := by
      intro K
      rw [Ideal.mapHom_apply]
      change Ideal.map (e : R₁ →+* R₂) (Ideal.map (e.symm : R₂ →+* R₁) K) = K
      rw [Ideal.map_map,
        show (e : R₁ →+* R₂).comp (e.symm : R₂ →+* R₁) = RingHom.id R₂ from
          RingHom.ext fun x => e.apply_symm_apply x,
        Ideal.map_id]
    refine ⟨fun I J h => ?_, fun J => ⟨Ideal.map (e.symm : R₂ →+* R₁) J, hright J⟩⟩
    have h2 := congrArg (fun K => Ideal.map (e.symm : R₂ →+* R₁) K) h
    rwa [hleft I, hleft J] at h2)

end Abstract

section NumberField

open NumberField

variable {A₁ A₂ B₁ B₂ : Type*} [Field A₁] [NumberField A₁]
    [Field A₂] [NumberField A₂] [Field B₁] [NumberField B₁] [Field B₂] [NumberField B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂]

/-- **Compatibility of the induced maps of rings of integers.**

If `μ : B₁ ≃+* B₂` carries the image of `A₁` into that of `A₂` through `μ₀ : A₁ ≃+* A₂`, then the
induced isomorphism `𝓞 B₁ ≃+* 𝓞 B₂` carries the image of `𝓞 A₁` into that of `𝓞 A₂` through the
induced isomorphism `𝓞 A₁ ≃+* 𝓞 A₂`. -/
lemma ringOfIntegersEquiv_algebraMap (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (x : NumberField.RingOfIntegers A₁) :
    NK.Reconstruct.ringOfIntegersEquiv μ
        (algebraMap (NumberField.RingOfIntegers A₁) (NumberField.RingOfIntegers B₁) x) =
      algebraMap (NumberField.RingOfIntegers A₂) (NumberField.RingOfIntegers B₂)
        (NK.Reconstruct.ringOfIntegersEquiv μ₀ x) := by
  apply NumberField.RingOfIntegers.ext
  simp only [NK.Reconstruct.ringOfIntegersEquiv_apply,
    show (algebraMap (NumberField.RingOfIntegers A₁) (NumberField.RingOfIntegers B₁))
      = NumberField.RingOfIntegers.mapRingHom (algebraMap A₁ B₁) from rfl,
    show (algebraMap (NumberField.RingOfIntegers A₂) (NumberField.RingOfIntegers B₂))
      = NumberField.RingOfIntegers.mapRingHom (algebraMap A₂ B₂) from rfl,
    NumberField.RingOfIntegers.mapRingHom_apply]
  exact hμ _

/-- **The prime below the transported prime is the transported prime below.** -/
lemma under_map_ringOfIntegersEquiv (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (q : Ideal (NumberField.RingOfIntegers B₁)) :
    (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
        (NumberField.RingOfIntegers A₂) =
      Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ₀)
        (q.under (NumberField.RingOfIntegers A₁)) := by
  exact comap_map_eq_map_comap _ _ _ _ (fun x => ringOfIntegersEquiv_algebraMap μ μ₀ hμ x) q

/-- **The ramification index is preserved by an isomorphism of the extensions.**

For `q` a nonzero prime of `𝓞 B₁`, the ramification index of the transported prime
`μ(q) = Ideal.map (ringOfIntegersEquiv μ) q` over `𝓞 A₂` equals that of `q` over `𝓞 A₁`. -/
lemma ramificationIdx_map_ringOfIntegersEquiv (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (q : Ideal (NumberField.RingOfIntegers B₁)) [q.IsPrime] (hq0 : q ≠ ⊥) :
    (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).ramificationIdx
        (NumberField.RingOfIntegers A₂) =
      q.ramificationIdx (NumberField.RingOfIntegers A₁) := by
  let φ : NumberField.RingOfIntegers B₁ →+* NumberField.RingOfIntegers B₂ :=
    NK.Reconstruct.ringOfIntegersEquiv μ
  let φ₀ : NumberField.RingOfIntegers A₁ →+* NumberField.RingOfIntegers A₂ :=
    NK.Reconstruct.ringOfIntegersEquiv μ₀
  let f₁ : NumberField.RingOfIntegers A₁ →+* NumberField.RingOfIntegers B₁ := algebraMap _ _
  let f₂ : NumberField.RingOfIntegers A₂ →+* NumberField.RingOfIntegers B₂ := algebraMap _ _
  change (Ideal.map φ q).ramificationIdx (NumberField.RingOfIntegers A₂) =
    q.ramificationIdx (NumberField.RingOfIntegers A₁)
  have hφ : ∀ x : NumberField.RingOfIntegers A₁, φ (f₁ x) = f₂ (φ₀ x) :=
    fun x => ringOfIntegersEquiv_algebraMap μ μ₀ hμ x
  have hcomp : f₂.comp φ₀ = φ.comp f₁ := RingHom.ext fun x => (hφ x).symm
  have hφinj : Function.Injective φ := (NK.Reconstruct.ringOfIntegersEquiv μ).injective
  have hunder : (Ideal.map φ q).under (NumberField.RingOfIntegers A₂) =
      Ideal.map φ₀ (q.under (NumberField.RingOfIntegers A₁)) :=
    under_map_ringOfIntegersEquiv μ μ₀ hμ q
  have hp0 : Ideal.map f₁ (q.under (NumberField.RingOfIntegers A₁)) ≠ ⊥ := by
    rw [Ideal.under_def]
    exact Ideal.map_ne_bot_of_ne_bot
      (Ideal.IsIntegral.comap_ne_bot (NumberField.RingOfIntegers A₁) hq0)
  have hq'0 : Ideal.map φ q ≠ ⊥ := fun h =>
    hq0 ((Ideal.map_eq_bot_iff_of_injective hφinj).mp h)
  haveI : (Ideal.map φ q).IsPrime :=
    Ideal.map_isPrime_of_equiv (NK.Reconstruct.ringOfIntegersEquiv μ)
  have hmap : Ideal.map f₂ ((Ideal.map φ q).under (NumberField.RingOfIntegers A₂)) =
      Ideal.map φ (Ideal.map f₁ (q.under (NumberField.RingOfIntegers A₁))) := by
    rw [hunder, Ideal.map_map, hcomp, ← Ideal.map_map]
  have hp0' : Ideal.map f₂ ((Ideal.map φ q).under (NumberField.RingOfIntegers A₂)) ≠ ⊥ :=
    fun h => hp0 ((Ideal.map_eq_bot_iff_of_injective hφinj).mp (hmap ▸ h))
  calc (Ideal.map φ q).ramificationIdx (NumberField.RingOfIntegers A₂)
      = multiplicity (Ideal.map φ q)
          (Ideal.map f₂ ((Ideal.map φ q).under (NumberField.RingOfIntegers A₂))) :=
        Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hp0'
    _ = multiplicity (Ideal.map φ q)
          (Ideal.map φ (Ideal.map f₁ (q.under (NumberField.RingOfIntegers A₁)))) := by
        rw [hmap]
    _ = multiplicity q (Ideal.map f₁ (q.under (NumberField.RingOfIntegers A₁))) :=
        multiplicity_map_eq (idealMapRingEquiv (NK.Reconstruct.ringOfIntegersEquiv μ))
    _ = q.ramificationIdx (NumberField.RingOfIntegers A₁) :=
        (Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hp0).symm

/-- **The inertia degree is preserved by an isomorphism of the extensions.**

For `q` a nonzero prime of `𝓞 B₁`, the inertia degree of the transported prime
`μ(q) = Ideal.map (ringOfIntegersEquiv μ) q` over `𝓞 A₂` equals that of `q` over `𝓞 A₁`. -/
lemma inertiaDeg_map_ringOfIntegersEquiv (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (q : Ideal (NumberField.RingOfIntegers B₁)) [hq : q.IsPrime] (hq0 : q ≠ ⊥) :
    (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).inertiaDeg
        (NumberField.RingOfIntegers A₂) =
      q.inertiaDeg (NumberField.RingOfIntegers A₁) := by
  have hunder : (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
        (NumberField.RingOfIntegers A₂) =
      Ideal.map (↑(NK.Reconstruct.ringOfIntegersEquiv μ₀) :
        NumberField.RingOfIntegers A₁ →+* NumberField.RingOfIntegers A₂)
        (q.under (NumberField.RingOfIntegers A₁)) :=
    under_map_ringOfIntegersEquiv μ μ₀ hμ q
  have hJ : Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q =
      Ideal.map (↑(NK.Reconstruct.ringOfIntegersEquiv μ) :
        NumberField.RingOfIntegers B₁ →+* NumberField.RingOfIntegers B₂) q := rfl
  have hφinj : Function.Injective (NK.Reconstruct.ringOfIntegersEquiv μ) :=
    (NK.Reconstruct.ringOfIntegersEquiv μ).injective
  have hφ₀inj : Function.Injective
      (↑(NK.Reconstruct.ringOfIntegersEquiv μ₀) :
        NumberField.RingOfIntegers A₁ →+* NumberField.RingOfIntegers A₂) := fun x y h =>
    (NK.Reconstruct.ringOfIntegersEquiv μ₀).injective h
  have hp0 : q.under (NumberField.RingOfIntegers A₁) ≠ ⊥ :=
    Ideal.under_ne_bot (NumberField.RingOfIntegers A₁) hq0
  have hq'0 : Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q ≠ ⊥ := fun h =>
    hq0 ((Ideal.map_eq_bot_iff_of_injective hφinj).mp h)
  have hp'0 : (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
      (NumberField.RingOfIntegers A₂) ≠ ⊥ := by
    rw [hunder]
    exact fun h => hp0 ((Ideal.map_eq_bot_iff_of_injective hφ₀inj).mp h)
  haveI hqM : q.IsMaximal := hq.isMaximal hq0
  haveI hpM : (q.under (NumberField.RingOfIntegers A₁)).IsMaximal :=
    (inferInstance : (q.under (NumberField.RingOfIntegers A₁)).IsPrime).isMaximal hp0
  haveI hq'M : (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).IsMaximal :=
    (Ideal.map_isPrime_of_equiv (NK.Reconstruct.ringOfIntegersEquiv μ)).isMaximal hq'0
  haveI hp'M : ((Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
      (NumberField.RingOfIntegers A₂)).IsMaximal :=
    (inferInstance : ((Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
      (NumberField.RingOfIntegers A₂)).IsPrime).isMaximal hp'0
  rw [Ideal.inertiaDeg_eq_of_isMaximal (q.under (NumberField.RingOfIntegers A₁)) q,
    Ideal.inertiaDeg_eq_of_isMaximal
      ((Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
        (NumberField.RingOfIntegers A₂))
      (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q)]
  refine (Algebra.finrank_eq_of_equiv_equiv
    (Ideal.quotientEquiv (q.under (NumberField.RingOfIntegers A₁))
      ((Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
        (NumberField.RingOfIntegers A₂))
      (NK.Reconstruct.ringOfIntegersEquiv μ₀) hunder)
    (Ideal.quotientEquiv q (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q)
      (NK.Reconstruct.ringOfIntegersEquiv μ) hJ) ?_).symm
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [Ideal.quotientEquiv_mk,
    Ideal.Quotient.algebraMap_mk_of_liesOver
      (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q)
      ((Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
        (NumberField.RingOfIntegers A₂)),
    Ideal.Quotient.algebraMap_mk_of_liesOver q (q.under (NumberField.RingOfIntegers A₁)),
    Ideal.quotientEquiv_mk]
  exact congrArg (Ideal.Quotient.mk (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q))
    (ringOfIntegersEquiv_algebraMap μ μ₀ hμ a).symm

/-- **The `asIdeal` of the transported prime.** -/
lemma primeTransport_asIdeal (μ : B₁ ≃+* B₂) (P : NK.Chebotarev.PrimeIdeal B₁) :
    (NK.Reconstruct.primeTransport μ P).asIdeal =
      Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) P.asIdeal := rfl

/-- **The local degree `e · f` is invariant under an isomorphism of number field extensions.**

Let `A₁ → B₁` and `A₂ → B₂` be extensions of number fields and let `μ : B₁ ≃+* B₂` be a field
isomorphism compatible with an isomorphism `μ₀ : A₁ ≃+* A₂` of the base fields.  Then for every
prime `P` of `𝓞 B₁` the local degree `e(P) · f(P)` of `P` over `A₁` equals that of the
corresponding prime `μ(P)` of `𝓞 B₂` over `A₂`. -/
theorem localDegree_primeTransport {A₁ A₂ B₁ B₂ : Type*} [Field A₁] [NumberField A₁]
    [Field A₂] [NumberField A₂] [Field B₁] [NumberField B₁] [Field B₂] [NumberField B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂] (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (P : NK.Chebotarev.PrimeIdeal B₁) (𝔭 : NK.Chebotarev.PrimeIdeal A₁)
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) :
    P.asIdeal.ramificationIdx (NumberField.RingOfIntegers A₁) *
        P.asIdeal.inertiaDeg (NumberField.RingOfIntegers A₁) =
      (NK.Reconstruct.primeTransport μ P).asIdeal.ramificationIdx
          (NumberField.RingOfIntegers A₂) *
        (NK.Reconstruct.primeTransport μ P).asIdeal.inertiaDeg
          (NumberField.RingOfIntegers A₂) := by
  rw [primeTransport_asIdeal μ P,
    ramificationIdx_map_ringOfIntegersEquiv μ μ₀ hμ P.asIdeal P.ne_bot,
    inertiaDeg_map_ringOfIntegersEquiv μ μ₀ hμ P.asIdeal P.ne_bot]

end NumberField

end NK.ReconstructField

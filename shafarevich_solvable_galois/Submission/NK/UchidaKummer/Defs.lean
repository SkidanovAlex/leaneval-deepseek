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
import Submission.NK.LocalAnabelian.Kummer.Defs
import Submission.NK.Reconstruct.PlaceCorrespondence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer

open IsDedekindDomain

noncomputable section

/-! ## Local degrees and completely split primes -/

section LocalDegrees

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The local degree** `[L_𝔓 : K_𝔭] = e(𝔓|𝔭) · f(𝔓|𝔭)`, written multiplicatively as in
`NK.Reconstruct.LocalCorrespondence.localDegree`. -/
def localDeg (P : NK.Chebotarev.PrimeIdeal L) (p : NK.Chebotarev.PrimeIdeal K) : ℕ :=
  P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
    P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)

/-- The primes of `𝓞 L` above the prime `p` of `𝓞 K`. -/
def primesAbove (p : NK.Chebotarev.PrimeIdeal K) : Set (NK.Chebotarev.PrimeIdeal L) :=
  {P | P.asIdeal.LiesOver p.asIdeal}

/-- **`p` splits completely in `L / K`**: the number of primes of `𝓞 L` above `p` is the degree
`[L : K]`, equivalently (for `L/K` Galois) every such prime is unramified of residue degree one.

This is the predicate of
`Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely`. -/
def SplitsCompletely (p : NK.Chebotarev.PrimeIdeal K) : Prop :=
  (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L

/-- The predicate `SplitsCompletely` is the contraction of the defining condition. -/
theorem splitsCompletely_iff (p : NK.Chebotarev.PrimeIdeal K) :
    SplitsCompletely (L := L) p ↔
      (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L :=
  Iff.rfl

/-- The primes in `primesAbove` are exactly the primes lying over `p`. -/
theorem mem_primesAbove {p : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal L} :
    P ∈ primesAbove (L := L) p ↔ P.asIdeal.LiesOver p.asIdeal :=
  Iff.rfl

/-- **The prescribed local degree condition of §5.**  The extension `L/K` has local degree
`a i` at the place `𝔭 i`: every prime of `𝓞 L` above `𝔭 i` has `e · f = a i`. -/
def HasLocalDegrees {ι : Type*} (𝔭 : ι → NK.Chebotarev.PrimeIdeal K) (a : ι → ℕ) : Prop :=
  ∀ i : ι, ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver (𝔭 i).asIdeal →
    localDeg P (𝔭 i) = a i

/-- Unfolding of `HasLocalDegrees`. -/
theorem hasLocalDegrees_iff {ι : Type*} (𝔭 : ι → NK.Chebotarev.PrimeIdeal K) (a : ι → ℕ) :
    HasLocalDegrees (L := L) 𝔭 a ↔
      ∀ i : ι, ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver (𝔭 i).asIdeal →
        localDeg P (𝔭 i) = a i :=
  Iff.rfl

end LocalDegrees

/-! ## Full-density sets of primes -/

/-- **A set of primes of full Dirichlet density**: its complement has Dirichlet density `0`. -/
def HasFullDensity (K : Type*) [Field K] [NumberField K]
    (R : Set (NK.Chebotarev.PrimeIdeal K)) : Prop :=
  NumberField.Set.HasDirichletDensity Rᶜ 0

/-- Unfolding of `HasFullDensity`. -/
theorem hasFullDensity_iff (K : Type*) [Field K] [NumberField K]
    (R : Set (NK.Chebotarev.PrimeIdeal K)) :
    HasFullDensity K R ↔ NumberField.Set.HasDirichletDensity Rᶜ 0 :=
  Iff.rfl

/-! ## The Kummer-theoretic inputs of §5 -/

/-- The subgroup of `ℓ`-th powers in the unit group of a field. -/
def ellPowSubgroup (k : Type*) [Field k] (ℓ : ℕ) : Subgroup kˣ :=
  (powMonoidHom ℓ : kˣ →* kˣ).range

section KummerInputs

variable (K : Type*) [Field K] [NumberField K]

/-- **The local `ℓ`-power class of a global unit.**  For a finite prime `𝔮` of `K`, this is the
composite `Kˣ → K_𝔮ˣ → K_𝔮ˣ / (K_𝔮ˣ)^ℓ`. -/
def localPowClass (ℓ : ℕ) (𝔮 : NK.Chebotarev.PrimeIdeal K) :
    Kˣ →* (𝔮.adicCompletion K)ˣ ⧸ ellPowSubgroup (𝔮.adicCompletion K) ℓ :=
  (QuotientGroup.mk' (ellPowSubgroup (𝔮.adicCompletion K) ℓ)).comp
    (Units.map (algebraMap K (𝔮.adicCompletion K)).toMonoidHom)

/-- **Weak approximation** for a number field at a finite set of finite primes: the diagonal
image of `K` in `∏_{𝔮 ∈ S} K_𝔮` is dense.

This is the approximation theorem of Neukirch, *Algebraic Number Theory*, Chap. II, 5.7 (the
"Chinese remainder theorem" quoted in the proof of §5's Prop. `K^x/K^ell local surjection`).  It is
the analytic/algebraic input behind `IsKummerSurjective`. -/
def IsWeakApproximation (K : Type*) [Field K] [NumberField K]
    (S : Finset (NK.Chebotarev.PrimeIdeal K)) : Prop :=
  DenseRange fun a : K => fun 𝔮 : S => algebraMap K (𝔮.1.adicCompletion K) a

/-- The subgroup of `ℓ`-th powers of the unit group of a completion is open.  This is the local
input of the proof of `IsKummerSurjective`: `K_𝔮ˣ/(K_𝔮ˣ)^ℓ` is finite (from the structure theory
`K_𝔮ˣ ≅ ℤ × μ × U¹`, `U¹ ≅ ℤ_p^d`), so `(K_𝔮ˣ)^ℓ` is a closed subgroup of finite index. -/
def IsOpenEllPowSubgroup (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) : Prop :=
  ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K,
    IsOpen ((ellPowSubgroup (𝔮.adicCompletion K) ℓ : Subgroup (𝔮.adicCompletion K)ˣ) :
      Set (𝔮.adicCompletion K)ˣ)

/-- **The Kummer local surjection of §5** (nu2d, Proposition `K^x/K^ell local surjection`).

For a number field `K` and a finite set `S` of finite primes, the map
`Kˣ / (Kˣ)^ℓ → ∏_{𝔮 ∈ S} K_𝔮ˣ / (K_𝔮ˣ)^ℓ` is surjective: every tuple of local `ℓ`-power classes
is the diagonal image of a global unit class.

In the paper this is deduced from the weak approximation theorem for number fields (the diagonal
image of `K` in `∏_{𝔮 ∈ S} K_𝔮` is dense, and the `ℓ`-th power subgroups are open); the Chinese
remainder theorem is quoted in Neukirch's *Algebraic Number Theory*, Chap. II, 5.7.

It is *not* used to prove the present file's theorems — it is the input of the differentiation
lemma `IsDifferentiable`. -/
def IsKummerSurjective (ℓ : ℕ) (S : Finset (NK.Chebotarev.PrimeIdeal K)) : Prop :=
  ∀ y : ∀ 𝔮 : S,
      (𝔮.1.adicCompletion K)ˣ ⧸ ellPowSubgroup (𝔮.1.adicCompletion K) ℓ,
    ∃ b : Kˣ, ∀ 𝔮 : S, localPowClass K ℓ 𝔮.1 b = y 𝔮

end KummerInputs

/-- **The local Kummer dichotomy** (the local content of §5's differentiation lemma).

For a Kummer extension `L = K(a^{1/ℓ})` of `K` inside `K'`, a finite prime `𝔭` of `K` splits
completely in `L` — equivalently every prime `P` of `𝓞 L` above `𝔭` has `e · f = 1` — exactly when
`a` is an `ℓ`-th power in the completion `K_𝔭`.

This is the statement that makes the Kummer method work: it converts the `ℓ`-divisibility of the
local classes of an element of `Kˣ` into the splitting/ramification behaviour of `K(a^{1/ℓ})`. -/
def IsKummerLocalDichotomy (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) : Prop :=
  ∀ (a : Kˣ) (L : IntermediateField K K') (_ : FiniteDimensional K L) (_ : NumberField ↥L),
    L = NK.LocalAnabelian.kummerField (K' := K') ℓ a → ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K,
      ((∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver 𝔮.asIdeal →
          localDeg P 𝔮 = 1) ↔
        ∃ b : (𝔮.adicCompletion K)ˣ,
          algebraMap K (𝔮.adicCompletion K) (a : K) = (b : 𝔮.adicCompletion K) ^ ℓ)

/-! ## The differentiation lemma of §5 -/

section Differentiation

variable (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K'] [Algebra K K']

/-- **The differentiation lemma of §5** (nu2d, Lemma `lem:ell prime differentiation`), in the
separable-closure setting.

Let `K` be a number field containing `μ_ℓ` (the containment is not part of this definition: it is
needed for the proof, via Kummer theory; for `Ω = K̄` the constructibility of the relevant Kummer
extensions inside `K'` is automatic).  For any finite list `𝔭` of distinct finite primes of `K`
and any prescription `a : Fin n → ℕ` of non-negative exponents, there is a finite extension
`L / K` inside `K'` whose local degree at `𝔭 i` is `ℓ ^ (a i)` for every `i`.

The extension need *not* be Galois (the paper remarks this explicitly). -/
def IsDifferentiable (ℓ : ℕ) : Prop :=
  ∀ (n : ℕ) (𝔭 : Fin n → NK.Chebotarev.PrimeIdeal K), Function.Injective 𝔭 →
    ∀ a : Fin n → ℕ,
      ∃ (L : IntermediateField K K') (_ : FiniteDimensional K L) (_ : NumberField ↥L),
        HasLocalDegrees (L := ↥L) 𝔭 fun i => ℓ ^ a i

/-- **The Kummer machinery over all finite intermediate fields.**

This is the uniform form of the two Kummer inputs of §5, quantified over every finite intermediate
field `E` of `K'/K` *with its own separable closure* `K'`.  The base change is essential: §5's
differentiation lemma is proved by induction, and after exhibiting `K(α^{1/ℓ})` with local degree
`ℓ` at `𝔭` one re-applies the construction with `K(α^{1/ℓ})` as the base field.  Working with a
fixed base field `K` only yields composita of radicals of `K`, whose local degree at a prime `𝔭`
with `ℓ ∤ 𝔭` and `μ_ℓ ⊆ K` is bounded by `ℓ ^ dim_{𝔽_ℓ} K_𝔭ˣ/(K_𝔭ˣ)^ℓ = ℓ ^ 2`.

The four components are

* `μ_ℓ ⊆ E`;
* the local Kummer surjection `IsKummerSurjective E ℓ S` for every finite `S`
  (§5 Prop. `K^x/K^ell local surjection`);
* a local unit at each prime of `E` which is not an `ℓ`-th power (this is what makes the
  differentiation *separate* the primes);
* the local dichotomy `IsKummerLocalDichotomy E K' ℓ`. -/
def HasKummerMachinery (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) : Prop :=
  ∀ (E : IntermediateField K K') (_ : FiniteDimensional K E) (_ : NumberField ↥E)
    (_ : IsSepClosure ↥E K'),
    (∃ ζ : ↥E, IsPrimitiveRoot ζ ℓ) ∧
    (∀ S : Finset (NK.Chebotarev.PrimeIdeal ↥E), IsKummerSurjective ↥E ℓ S) ∧
    (∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥E, ∃ u : (𝔭.adicCompletion ↥E)ˣ,
      ∀ b : (𝔭.adicCompletion ↥E)ˣ, b ^ ℓ ≠ u) ∧
    IsKummerLocalDichotomy ↥E K' ℓ

end Differentiation

/-! ## The prime-identification step of §5 -/

section PrimeIdentification

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The prime-identification input of the Kummer route** (§5 Lemmas `lem:ell prime
differentiation` + `lem:alpha identifies with sigma on primes`).

The Kummer method produces a `MapsBase` field isomorphism `σ : K₂' ≃+* K₁'` together with:

* the *level correspondence* `AgreesOnLevels ϕ hϕ σ hσ`: `σ` carries the finite Galois
  subextensions of `K₁'/K₁` onto the subextensions of `K₂'/K₂` corresponding to them under `ϕ`
  (this is the σ-free content of CoNF (12.1.9), i.e. input (A) of the development);
* the *place identification*: outside a set of primes of Dirichlet density zero, `σ` realises the
  place correspondence `a` of `ϕ`.

The paper's `lem:alpha identifies with sigma on primes` produces exactly this: an isomorphism
`σ : K₁' → K₂'` induced by a base-field isomorphism and carrying `α(𝔓)` to `𝔓` for every place
`𝔓` over the primes of a full-density set.  The *finiteness* of the set of isomorphisms
`K₁ → K₂` is what upgrades "for every finite `R' ⊆ R`" to "for all of `R`".

The conclusion `Conjugates σ ϕ` is *not* part of the input; the upgrade from the density-one
place identification to the group-theoretic statement is
`NK.UchidaKummer.Identification.conjugates_of_kummerPrimeIdentification`, and it is where the
completely split primes enter (`NK.UchidaKummer.SplitPrimes`). -/
def KummerPrimeIdentification {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop :=
  ∃ (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
    NK.Reconstruct.AgreesOnLevels ϕ hϕ σ hσ ∧
      ∃ R : Set (NK.Chebotarev.PrimeIdeal K₁), HasFullDensity K₁ R ∧
        ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
          Submission.NeukirchUchida.primeOf A.1 A.2 ∈ R →
            (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1

end PrimeIdentification

/-! ## The σ-free identification step of §5 -/

section PrimeMapStep

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}

/-- **§5 Lemma 5.2 (`lem:alpha identifies with sigma on primes`), σ-free form.**

There is an isomorphism `τ` of the *base fields* `K₁ ≃+* K₂` whose induced correspondence of finite
primes agrees with the prime correspondence `a.primeMap` of the local correspondence outside a set
of primes of Dirichlet density zero.

This is *σ-free*: it speaks of a base-field isomorphism, not of a field isomorphism `K₂' ≃+* K₁'`.

**Recorded negative finding.**  Two reviewers of the derivation
`KummerPrimeMapStep → ∃ σ, Conjugates σ ϕ` both judged it insufficient: prime-level agreement does
not give the *place*-level realization, because for a place `A` over `𝔭 ∈ R` one only learns that
`a.placeMap A` and `A.comap σ` both lie over `τ 𝔭`, and the Galois group acts transitively on the
places over `τ 𝔭`, leaving an uncontrolled twist.  In this workspace prime compatibility and place
realization are indeed independent inputs (`Work/ReconstructField/Targets.lean`).  So the honest
input of §5's identification step is necessarily *place*-level: `KummerPrimeIdentification`. -/
def KummerPrimeMapStep (ℓ : ℕ) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop :=
  ∃ (τ : K₁ ≃+* K₂) (R : Set (NK.Chebotarev.PrimeIdeal K₁)), HasFullDensity K₁ R ∧
    ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁, 𝔭 ∈ R →
      a.primeMap 𝔭 = NK.Reconstruct.primeTransport τ 𝔭

end PrimeMapStep

/-- **The weak Neukirch–Uchida theorem at levels** (§6 in the form §5 consumes), *σ-free*.

For every finite Galois level `L` of `K₁'/K₁`, the corresponding level `levelMap ϕ L` of `K₂'/K₂`
is ring-isomorphic to `L`, compatibly with the two base fields (`MapsBaseLevel`).  No field
isomorphism of the *separable closures* is asserted: this is a family of isomorphisms of finite
levels only.

§5 obtains this by applying its weak theorem to the pair `(L, levelMap ϕ L)` (via the induced
isomorphism `Gal(K₁'/L) ≃* Gal(K₂'/levelMap ϕ L)`); the base compatibility is the step of §5's
`lem:alpha identifies with sigma on primes` that invokes the arithmetic equivalence
"the Galois closure of `K₂` intersected with `Ω₂` is `K₂`", which is the classical Perlis input.

**Caveat.**  As an input of §5's identification step this is *not* sufficient by itself: §5's
compactness argument needs the level isomorphisms to be mutually compatible (there they are the
restrictions of a single element of `Gal(K₂'/K₂)`), and an arbitrary family of level
isomorphisms need not be.  Adding that compatibility makes the datum equivalent to a single
`MapsBase` isomorphism, i.e. to the conclusion.  The definition is kept as the precise vocabulary
of "§6 at levels". -/
def IsWeakUchidaLevels {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (ℓ : ℕ)
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ) : Prop :=
  ∀ (L : IntermediateField K₁ K₁') (_ : FiniteDimensional K₁ L) (_ : IsGalois K₁ L)
    (_ : NumberField ↥L),
    ∃ (τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L)),
      NK.Reconstruct.MapsBaseLevel L (NK.Reconstruct.levelMap ϕ L) τ

/-! ## The weak Neukirch–Uchida theorem of §6 -/

/-- **Uchida's Kummer-theoretic embedding problem** (nu2d §6, Lemma `lem:embedding problem`).

For a finite Galois extension `L / ℚ` and a finite set `S` of primes of `L` there is a finite
abelian extension `M / L`, Galois over `ℚ`, of degree `ℓ ^ |Gal(L/ℚ)|` over `L`, in which every
prime of `S` splits completely.  (In the paper `Gal(M/L) ≅ 𝔽_ℓ[Gal(L/ℚ)]^n` as a module for
`Gal(L/ℚ)`; the module structure — which is what the arithmetic-equivalence argument uses — is
not recorded here, only the underlying group-theoretic content of degrees and splitting.)

The existence of the completely split primes used in the proof is unconditional in this workspace,
`Commons.NumberTheory.NumberField.exists_prime_splitsCompletely`; the rest of the proof is Kummer
theory (`IsKummerSurjective`). -/
def IsKummerEmbeddingProblem (ℓ : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L],
    (∃ ζ : L, IsPrimitiveRoot ζ ℓ) →
    ∀ (S : Finset (NK.Chebotarev.PrimeIdeal L)),
      ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra L M) (_ : FiniteDimensional L M)
        (_ : IsGalois L M),
        (∀ 𝔮 : S, SplitsCompletely (K := L) (L := M) 𝔮.1) ∧
        Nat.card Gal(M/L) = ℓ ^ Nat.card Gal(L/ℚ)

/-- **The weak Neukirch–Uchida theorem** (nu2d §6, Theorem `thm:uchida isomorphism`), in the
separable-closure case `Ω_i = K̄_i`, where the `ℓ`-sealed and abundance hypotheses are automatic
(a separable closure has no nontrivial finite extension, hence no `ℤ/ℓ`-extension in which places
can split completely; and its completions are separably closed, hence abundant).

Number fields containing `μ_ℓ` with isomorphic absolute Galois groups are isomorphic.  The
existence of the isomorphism is what §6 proves, from `IsKummerEmbeddingProblem` together with the
arithmetic-equivalence theory of Perlis. -/
def IsWeakUchida (ℓ : ℕ) : Prop :=
  ∀ (K₁ K₂ : Type) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (K₁' : Type) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂'],
    Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) → Nonempty (K₁ ≃+* K₂)

end

end NK.UchidaKummer

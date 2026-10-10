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
import Submission.Work.AbsoluteGalois.exists_hom_lift_iff_pullbackCocycle_mem_B2
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


namespace Work.SSGRoute

open Work.CohomologicalShrinking

attribute [local instance] Classical.decEq

/-! ## The projection `Γ(τ+1) ↠ Γ(τ)` -/

/-- The refined term at `τ + 1` is contained in the refined term at `τ`. -/
theorem refinedTerm_tauSucc_le (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    refinedTerm p P (tauSucc i j).1 (tauSucc i j).2 ≤ refinedTerm p P i j := by
  by_cases h : j < i
  · rw [tauSucc_of_lt h]
    exact refinedTerm_antitone_snd p P i j
  · rw [tauSucc_of_le (Nat.le_of_not_lt h), refinedTerm_one]
    exact le_sup_right

/-- The quotient map `F/Q →* F/P` for `Q = F^{(τ+1)} ≤ P = F^{(τ)}`. -/
noncomputable def flowQuotSucc (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2 →* flowQuotient p G m i j :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rw [Subgroup.comap_id]
    exact Subgroup.subgroupOf_mono _
      (refinedTerm_tauSucc_le p (Work.Shrinking.freeOperatorGroup G m) i j))

@[simp] theorem flowQuotSucc_mk (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (x : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
    flowQuotSucc p G m i j (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x :=
  QuotientGroup.map_mk' _ _ _ _ x

/-- The same, in the `QuotientGroup.mk` form used by `SSGRoute.LiftsFlowAt`. -/
theorem flowQuotSucc_mk_apply (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (x : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
    flowQuotSucc p G m i j
        (QuotientGroup.mk x : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2)
      = (QuotientGroup.mk x : flowQuotient p G m i j) :=
  QuotientGroup.map_mk' _ _ _ _ x

theorem flowQuotSucc_surjective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowQuotSucc p G m i j) := by
  intro a
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) a
  exact ⟨QuotientGroup.mk' _ x, by rw [flowQuotSucc_mk, hx]⟩

/-- The quotient map is `G`-equivariant for the descended actions. -/
theorem flowQuotSucc_smul (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) (g : G)
    (x : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) :
    flowQuotSucc p G m i j (g • x) = g • flowQuotSucc p G m i j x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) x
  have hP : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G _ g).surjective
  have hKP : (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = flowTerm p G m (tauSucc i j).1 (tauSucc i j).2 :=
    map_refinedTerm_eq p
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g)
      (tauSucc i j).1 (tauSucc i j).2
  have hKQ : (flowTerm p G m i j).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g).toMonoidHom
      = flowTerm p G m i j :=
    map_refinedTerm_eq p
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G m) g) i j
  have keyP : g • (QuotientGroup.mk'
        ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y)
      = QuotientGroup.mk'
        ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        (Work.Shrinking.subAut ⊤ g hP y) := by
    change Work.Shrinking.quotAut ⊤ (flowTerm p G m (tauSucc i j).1 (tauSucc i j).2) g hP hKP
      (QuotientGroup.mk' _ y) = _
    rw [Work.Shrinking.quotAut_mk]
  have keyQ : g • (QuotientGroup.mk'
        ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y)
      = QuotientGroup.mk'
        ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)))
        (Work.Shrinking.subAut ⊤ g hP y) := by
    change Work.Shrinking.quotAut ⊤ (flowTerm p G m i j) g hP hKQ
      (QuotientGroup.mk' _ y) = _
    rw [Work.Shrinking.quotAut_mk]
  rw [keyP, flowQuotSucc_mk]
  exact keyQ.symm

/-- The canonical projection `Γ(τ+1) = F(m)/F(m)^{(τ+1)} ⋊ G →* Γ(τ) = F(m)/F(m)^{(τ)} ⋊ G`. -/
noncomputable def flowGroupSucc (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowGroup p G m (tauSucc i j).1 (tauSucc i j).2 →* flowGroup p G m i j :=
  SemidirectProduct.map (flowQuotSucc p G m i j) (MonoidHom.id G)
    (fun g => MonoidHom.ext (fun x => flowQuotSucc_smul p G m i j g x))

@[simp] theorem flowGroupSucc_mk (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (a : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) (g : G) :
    flowGroupSucc p G m i j (SemidirectProduct.mk a g) =
      SemidirectProduct.mk (flowQuotSucc p G m i j a) g := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [flowGroupSucc, SemidirectProduct.map_left]
  · rw [flowGroupSucc, SemidirectProduct.map_right]; rfl

@[simp] theorem flowGroupSucc_left (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (y : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) :
    (flowGroupSucc p G m i j y).left = flowQuotSucc p G m i j y.left := by
  conv_lhs => rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]

@[simp] theorem flowGroupSucc_right (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (y : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) :
    (flowGroupSucc p G m i j y).right = y.right := by
  conv_lhs => rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]

@[simp] theorem flowGroupMap_left (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : flowGroup p G m i j) :
    (flowGroupMap p G i j Φ x).left = flowQuotMap p G i j Φ x.left := by
  conv_lhs => rw [show x = SemidirectProduct.mk x.left x.right from rfl]
  rw [flowGroupMap, SemidirectProduct.map_left]

@[simp] theorem flowGroupMap_right (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : flowGroup p G m i j) :
    (flowGroupMap p G i j Φ x).right = x.right := by
  conv_lhs => rw [show x = SemidirectProduct.mk x.left x.right from rfl]
  rw [flowGroupMap, SemidirectProduct.map_right, MonoidHom.id_apply]

theorem flowGroupSucc_surjective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowGroupSucc p G m i j) := by
  intro γ
  obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) γ.left
  refine ⟨SemidirectProduct.mk (QuotientGroup.mk' _ z) γ.right, ?_⟩
  rw [flowGroupSucc_mk, flowQuotSucc_mk, hz]

/-! ## `LiftsFlowAt` as the projection -/

/-- The generic form of `SSGRoute.LiftsFlowAt` (the two definitions are equal by `rfl`). -/
def LiftsFlowAtGen (p : ℕ) (G : Type*) [Group G] (m i j i' j' : ℕ)
    (y : flowGroup p G m i' j') (x : flowGroup p G m i j) : Prop :=
  y.right = x.right ∧
    ∃ z : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)),
      y.left = (QuotientGroup.mk z : flowQuotient p G m i' j') ∧
      x.left = (QuotientGroup.mk z : flowQuotient p G m i j)

/-- `LiftsFlowAt y x` is exactly `flowGroupSucc y = x`. -/
theorem liftsFlowAtGen_iff_flowGroupSucc (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (y : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) (x : flowGroup p G m i j) :
    LiftsFlowAtGen p G m i j (tauSucc i j).1 (tauSucc i j).2 y x ↔
      flowGroupSucc p G m i j y = x := by
  constructor
  · rintro ⟨hr, z, h1, h2⟩
    refine SemidirectProduct.ext ?_ ?_
    · show (flowGroupSucc p G m i j y).left = x.left
      conv_lhs => rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]
      rw [h1, flowQuotSucc_mk_apply, h2]
    · show (flowGroupSucc p G m i j y).right = x.right
      conv_lhs => rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]
      rw [hr]
  · intro h
    have hr : y.right = x.right := by
      have := congrArg SemidirectProduct.right h
      rwa [show (flowGroupSucc p G m i j y).right = y.right from by
        rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]] at this
    refine ⟨hr, ?_⟩
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective
      ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) y.left
    refine ⟨z, hz.symm, ?_⟩
    have h2 : flowQuotSucc p G m i j y.left = x.left := by
      have := congrArg SemidirectProduct.left h
      rwa [show (flowGroupSucc p G m i j y).left = flowQuotSucc p G m i j y.left from by
        rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupSucc_mk]] at this
    rw [← hz, flowQuotSucc_mk] at h2
    exact h2.symm

/-- `LiftsFlowAt` is exactly the vanishing of the projection `flowGroupSucc`. -/
theorem liftsFlowAt_iff_flowGroupSucc (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    (m i j : ℕ)
    (y : flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (x : flowGroup p (K ≃ₐ[ℚ] K) m i j) :
    SSGRoute.LiftsFlowAt y x ↔ flowGroupSucc p (K ≃ₐ[ℚ] K) m i j y = x :=
  liftsFlowAtGen_iff_flowGroupSucc p (K ≃ₐ[ℚ] K) m i j y x

/-! ## A section of `flowGroupSucc` -/

/-- A set-theoretic section of `flowGroupSucc`, normalized at `1`. -/
noncomputable def flowGroupSection (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2 := fun x =>
  if h : x = 1 then 1
  else Classical.choose (flowGroupSucc_surjective p G m i j x)

@[simp] theorem flowGroupSection_one (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowGroupSection p G m i j 1 = 1 := dif_pos rfl

theorem flowGroupSucc_section (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (x : flowGroup p G m i j) :
    flowGroupSucc p G m i j (flowGroupSection p G m i j x) = x := by
  rw [flowGroupSection]
  split
  · next h => rw [h, map_one]
  · next h => exact Classical.choose_spec (flowGroupSucc_surjective p G m i j x)

/-- The section `2`-cocycle of the projection `flowGroupSucc`, valued in its kernel. -/
noncomputable def kerSuccCocycleMul (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    {H : Type*} [Group H] (ρ : H →* flowGroup p G m i j)
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x) :
    H → H → ↥(flowGroupSucc p G m i j).ker := fun σ τ =>
  ⟨s (ρ σ) * s (ρ τ) * (s (ρ (σ * τ)))⁻¹, by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hs]
    group⟩

/-- The same cocycle, written additively. -/
noncomputable def kerSuccCocycle (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    {H : Type*} [Group H] (ρ : H →* flowGroup p G m i j)
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x) :
    H → H → Additive ↥(flowGroupSucc p G m i j).ker :=
  fun σ τ => Additive.ofMul (kerSuccCocycleMul p G m i j ρ s hs σ τ)

/-! ## The kernel map induced by a rank change and the correction cochain -/

/-- The quotient maps commute with the rank change `Φ`. -/
theorem flowQuotSucc_flowQuotMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) :
    (flowQuotSucc p G n i j).comp (flowQuotMap p G (tauSucc i j).1 (tauSucc i j).2 Φ) =
      (flowQuotMap p G i j Φ).comp (flowQuotSucc p G m i j) := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) x
  simp only [MonoidHom.comp_apply, flowQuotMap_mk, flowQuotSucc_mk]

/-- The projections commute with the rank change `Φ`. -/
theorem flowGroupSucc_flowGroupMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) :
    (flowGroupSucc p G n i j).comp (flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ) =
      (flowGroupMap p G i j Φ).comp (flowGroupSucc p G m i j) := by
  refine MonoidHom.ext fun x => ?_
  refine SemidirectProduct.ext ?_ ?_
  · simp only [MonoidHom.comp_apply, flowGroupSucc_left, flowGroupMap_left]
    exact DFunLike.congr_fun (flowQuotSucc_flowQuotMap p G i j Φ) x.left
  · simp only [MonoidHom.comp_apply, flowGroupSucc_right, flowGroupMap_right]

/-- The map induced by an operator map on the kernels of the projections. -/
noncomputable def flowGroupSuccKernelMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) :
    ↥(flowGroupSucc p G m i j).ker →* ↥(flowGroupSucc p G n i j).ker :=
  ((flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ).comp (Subgroup.subtype _)).codRestrict _
    (fun x => by
      rw [MonoidHom.mem_ker]
      show flowGroupSucc p G n i j (flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ
        (x : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)) = 1
      have h := DFunLike.congr_fun (flowGroupSucc_flowGroupMap p G i j Φ)
        (x : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
      simp only [MonoidHom.comp_apply] at h
      rw [h, x.2, map_one])


@[simp] theorem flowGroupSuccKernelMap_apply (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : ↥(flowGroupSucc p G m i j).ker) :
    ((flowGroupSuccKernelMap p G i j Φ x : ↥(flowGroupSucc p G n i j).ker) :
        flowGroup p G n (tauSucc i j).1 (tauSucc i j).2)
      = flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ
          (x : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) := rfl

/-- The correction cochain `β_σ = Φ_{τ+1}(s_m(ρ σ)) s_n(ρ' σ)^{-1}` of the naturality of the
section cocycle. -/
noncomputable def kerSuccBeta (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) {H : Type*} [Group H]
    (ρ : H →* flowGroup p G m i j) (ρ' : H →* flowGroup p G n i j)
    (hρ : ∀ σ : H, ρ' σ = flowGroupMap p G i j Φ (ρ σ))
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (s' : flowGroup p G n i j → flowGroup p G n (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x)
    (hs' : ∀ x, flowGroupSucc p G n i j (s' x) = x) :
    H → ↥(flowGroupSucc p G n i j).ker := fun σ =>
  ⟨flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ (s (ρ σ)) * (s' (ρ' σ))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs']
    have h := DFunLike.congr_fun (flowGroupSucc_flowGroupMap p G i j Φ) (s (ρ σ))
    simp only [MonoidHom.comp_apply] at h
    rw [h, hs, hρ σ, mul_inv_cancel]⟩

/-! ## The lifting criterion for `flowGroupSucc` -/

/-- The pullback of the abstract `sectionCocycle` is the cocycle `kerSuccCocycle`. -/
theorem pullbackCocycle_sectionCocycle_eq (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    {H : Type*} [Group H] (ρ : H →* flowGroup p G m i j)
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x) :
    Work.AbsoluteGalois.pullbackCocycle ρ
        (Work.AbsoluteGalois.sectionCocycle (flowGroupSucc p G m i j) s hs)
      = fun x : H × H => kerSuccCocycle p G m i j ρ s hs x.1 x.2 := by
  funext x
  obtain ⟨σ, τ⟩ := x
  rw [Work.AbsoluteGalois.pullbackCocycle_apply]
  apply Additive.ofMul.injective
  have hK : s (ρ σ) * s (ρ τ) * (s (ρ (σ * τ)))⁻¹
      = s (ρ σ) * s (ρ τ) * (s (ρ σ * ρ τ))⁻¹ := by
    rw [map_mul ρ σ τ]
  exact Subtype.ext hK.symm

theorem exists_lift_iff_kerSuccCocycle (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    {H : Type*} [Group H] (ρ : H →* flowGroup p G m i j)
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x) (h1 : s 1 = 1)
    (hcomm : ∀ a b : ↥(flowGroupSucc p G m i j).ker, a * b = b * a) :
    letI : CommGroup ↥(flowGroupSucc p G m i j).ker :=
      { (inferInstance : Group ↥(flowGroupSucc p G m i j).ker) with mul_comm := hcomm }
    letI : DistribMulAction (flowGroup p G m i j) (Additive ↥(flowGroupSucc p G m i j).ker) :=
      Work.AbsoluteGalois.kernelAction (flowGroupSucc p G m i j) s hs h1 hcomm
    letI : DistribMulAction H (Additive ↥(flowGroupSucc p G m i j).ker) :=
      DistribMulAction.compHom (Additive ↥(flowGroupSucc p G m i j).ker) ρ
    ((∃ ψ : H →* flowGroup p G m (tauSucc i j).1 (tauSucc i j).2,
        (flowGroupSucc p G m i j).comp ψ = ρ) ↔
      (fun x : H × H => kerSuccCocycle p G m i j ρ s hs x.1 x.2) ∈
        Work.GroupCohomology.B2 H (Additive ↥(flowGroupSucc p G m i j).ker)) := by
  letI : CommGroup ↥(flowGroupSucc p G m i j).ker :=
    { (inferInstance : Group ↥(flowGroupSucc p G m i j).ker) with mul_comm := hcomm }
  letI : DistribMulAction (flowGroup p G m i j) (Additive ↥(flowGroupSucc p G m i j).ker) :=
    Work.AbsoluteGalois.kernelAction (flowGroupSucc p G m i j) s hs h1 hcomm
  letI : DistribMulAction H (Additive ↥(flowGroupSucc p G m i j).ker) :=
    DistribMulAction.compHom (Additive ↥(flowGroupSucc p G m i j).ker) ρ
  have h := Work.AbsoluteGalois.exists_hom_lift_iff_pullbackCocycle_mem_B2
    (G := flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (Q := flowGroup p G m i j) (H := H)
    (flowGroupSucc p G m i j) s hs h1 hcomm ρ
  rwa [pullbackCocycle_sectionCocycle_eq p G m i j ρ s hs] at h

end Work.SSGRoute

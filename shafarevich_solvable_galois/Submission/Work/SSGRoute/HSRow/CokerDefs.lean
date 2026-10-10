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
import Submission.Work.SSGRoute.HSRow.Coords
import Submission.Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp
import Submission.Work.SSGRoute.HSTwoRow.procyclic_hypotheses
import Submission.Work.SSGRoute.PT.H2RowAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inverse transgression: the `Φ`-construction (definitions)

Vocabulary for the proof of `Work.SSGRoute.HSRow.coker_injects_H2loc`.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- `C = closure (zpowers σ)`. -/
abbrev Ccl (σ : Ω ≃ₐ[k] Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  Subgroup.topologicalClosure (Subgroup.zpowers σ)

/-- `σ` as an element of `C`. -/
def sigC (σ : Ω ≃ₐ[k] Ω) : ↥(Ccl k Ω σ) :=
  ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)⟩

@[simp] lemma sigC_coe (σ : Ω ≃ₐ[k] Ω) :
    ((sigC k Ω σ : ↥(Ccl k Ω σ)) : Ω ≃ₐ[k] Ω) = σ := rfl

/-- The locally constant `1`-cocycles on `I`. -/
abbrev Z1 (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) :=
  SSGRoute.lcCocycles p k Ω K M I

/-- The group-theoretic hypotheses on the pair `(I, σ)`. -/
structure Hcx (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) where
  A : ValuationSubring Ω
  hI : I ≤ SSGRoute.decomp k A
  hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I
  hσ : σ ∈ SSGRoute.decomp k A
  hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ)
  hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥

lemma conj_inv_mem (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) :
    ∀ n ∈ I, (γ : Ω ≃ₐ[k] Ω)⁻¹ * n * (γ : Ω ≃ₐ[k] Ω) ∈ I := by
  intro n hn
  have hγD : (γ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k H.A :=
    Work.SSGRoute.HS.CC_le_DD H.A σ H.hσ γ.2
  have h := H.hnorm (γ : Ω ≃ₐ[k] Ω)⁻¹ ((SSGRoute.decomp k H.A).inv_mem hγD) n hn
  simpa using h

/-- The conjugation action of `γ ∈ C` on `Z1`. -/
def tw1 (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) : ↥(Z1 p k Ω K M I) →ₗ[ZMod p] ↥(Z1 p k Ω K M I) where
  toFun z := ⟨h1locConjShift p k Ω K M (γ : Ω ≃ₐ[k] Ω) z.1,
    h1locConjShift_mem_lcCocycles p k Ω K M I (γ : Ω ≃ₐ[k] Ω)
      (conj_inv_mem p k Ω K M I σ H γ) z.2⟩
  map_add' z w := Subtype.ext ((h1locConjShift p k Ω K M (γ : Ω ≃ₐ[k] Ω)).map_add z.1 w.1)
  map_smul' c z := Subtype.ext ((h1locConjShift p k Ω K M (γ : Ω ≃ₐ[k] Ω)).map_smul c z.1)

@[simp] lemma tw1_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) (n : Ω ≃ₐ[k] Ω) :
    ((tw1 p k Ω K M I σ H γ z : ↥(Z1 p k Ω K M I)) : (Ω ≃ₐ[k] Ω) → M) n
      = SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
          • (z : (Ω ≃ₐ[k] Ω) → M) ((γ : Ω ≃ₐ[k] Ω)⁻¹ * n * (γ : Ω ≃ₐ[k] Ω)) := rfl

/-- The conjugation shift is multiplicative in the group element. -/
lemma h1locConjShift_comp (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (γ δ : Ω ≃ₐ[k] Ω) (f : (Ω ≃ₐ[k] Ω) → M) :
    h1locConjShift p k Ω K M γ (h1locConjShift p k Ω K M δ f)
      = h1locConjShift p k Ω K M (γ * δ) f := by
  funext n
  show SSGRoute.res k K γ • (SSGRoute.res k K δ • f (δ⁻¹ * (γ⁻¹ * n * γ) * δ))
    = SSGRoute.res k K (γ * δ) • f ((γ * δ)⁻¹ * n * (γ * δ))
  rw [show δ⁻¹ * (γ⁻¹ * n * γ) * δ = (γ * δ)⁻¹ * n * (γ * δ) from by group,
    map_mul, mul_smul]

lemma tw1_comp (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ δ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) :
    tw1 p k Ω K M I σ H γ (tw1 p k Ω K M I σ H δ z) = tw1 p k Ω K M I σ H (γ * δ) z := by
  refine Subtype.ext ?_
  exact h1locConjShift_comp p k Ω K M (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω) (z : (Ω ≃ₐ[k] Ω) → M)

lemma tw1_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    tw1 p k Ω K M I σ H (1 : ↥(Ccl k Ω σ)) = LinearMap.id := by
  refine LinearMap.ext fun z => Subtype.ext (funext fun n => ?_)
  simp only [tw1_apply, OneMemClass.coe_one, map_one, one_mul, inv_one, one_smul]
  rfl

lemma tw1_inv_comp (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) :
    tw1 p k Ω K M I σ H γ⁻¹ (tw1 p k Ω K M I σ H γ z) = z := by
  rw [tw1_comp, inv_mul_cancel]
  have h : tw1 p k Ω K M I σ H (1 : ↥(Ccl k Ω σ)) z = z := by
    rw [tw1_one]; rfl
  exact h

lemma tw1_comp_inv (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) :
    tw1 p k Ω K M I σ H γ (tw1 p k Ω K M I σ H γ⁻¹ z) = z := by
  rw [tw1_comp, mul_inv_cancel]
  have h : tw1 p k Ω K M I σ H (1 : ↥(Ccl k Ω σ)) z = z := by
    rw [tw1_one]; rfl
  exact h

/-- The conjugation action of `C` on `Z1`, as a homomorphism into the endomorphism monoid. -/
def twHom1 (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    ↥(Ccl k Ω σ) →* (↥(Z1 p k Ω K M I) →ₗ[ZMod p] ↥(Z1 p k Ω K M I)) where
  toFun := tw1 p k Ω K M I σ H
  map_one' := tw1_one p k Ω K M I σ H
  map_mul' γ δ := by
    refine LinearMap.ext fun z => ?_
    rw [Module.End.mul_apply]
    exact (tw1_comp p k Ω K M I σ H γ δ z).symm

/-- The conjugation action of `γ ∈ C` on `Z1`, as a linear equivalence. -/
def tw1e (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) : ↥(Z1 p k Ω K M I) ≃ₗ[ZMod p] ↥(Z1 p k Ω K M I) where
  toLinearMap := tw1 p k Ω K M I σ H γ
  invFun := tw1 p k Ω K M I σ H γ⁻¹
  left_inv z := tw1_inv_comp p k Ω K M I σ H γ z
  right_inv z := tw1_comp_inv p k Ω K M I σ H γ z

@[simp] lemma tw1e_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) :
    tw1e p k Ω K M I σ H γ z = tw1 p k Ω K M I σ H γ z := rfl

/-- The conjugation action of `C` on `Z1`, as a monoid homomorphism into its automorphism
group. -/
def twHom (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    ↥(Ccl k Ω σ) →* (↥(Z1 p k Ω K M I) ≃ₗ[ZMod p] ↥(Z1 p k Ω K M I)) where
  toFun := tw1e p k Ω K M I σ H
  map_one' := by
    refine LinearEquiv.ext fun z => Subtype.ext (funext fun n => ?_)
    simp only [tw1e_apply, tw1_apply, OneMemClass.coe_one, map_one, one_mul, inv_one,
      one_smul]
    rfl
  map_mul' γ δ := by
    refine LinearEquiv.ext fun z => ?_
    simp only [LinearEquiv.mul_apply, tw1e_apply]
    exact (tw1_comp p k Ω K M I σ H γ δ z).symm

lemma twHom_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) :
    twHom p k Ω K M I σ H γ z = tw1 p k Ω K M I σ H γ z := rfl

/-- The conjugation action is multiplicative in the group element, as an equality of linear
maps. -/
lemma tw1_comp_map (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ δ : ↥(Ccl k Ω σ)) :
    tw1 p k Ω K M I σ H (γ * δ) =
      (tw1 p k Ω K M I σ H γ).comp (tw1 p k Ω K M I σ H δ) := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply]
  exact (tw1_comp p k Ω K M I σ H γ δ z).symm

/-- Powers act by composition of the conjugation action. -/
lemma tw1_pow (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (j : ℕ) :
    tw1 p k Ω K M I σ H (γ ^ j) = (tw1 p k Ω K M I σ H γ) ^ j := by
  induction j with
  | zero =>
      rw [pow_zero, tw1_one, pow_zero]
      rfl
  | succ j ih =>
      rw [pow_succ', tw1_comp_map, ih, pow_succ', Module.End.mul_eq_comp]

/-- **The period.**  If `Z1` is finite, the conjugation action of `σ` on it has a positive
period `e`. -/
lemma exists_period (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    [Finite ↥(Z1 p k Ω K M I)] :
    ∃ e : ℕ, 0 < e ∧ ∀ z : ↥(Z1 p k Ω K M I),
      tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ e) z = z := by
  classical
  haveI : Fintype ↥(Z1 p k Ω K M I) := Fintype.ofFinite _
  let g : ↥(Z1 p k Ω K M I) → ↥(Z1 p k Ω K M I) := tw1 p k Ω K M I σ H (sigC k Ω σ)
  have hg_inj : Function.Injective g := by
    intro z w hzw
    have h := congrArg (fun x => tw1 p k Ω K M I σ H ((sigC k Ω σ))⁻¹ x) hzw
    simpa [g, tw1_inv_comp] using h
  have hg_surj : Function.Surjective g := Finite.surjective_of_injective hg_inj
  let T : Equiv.Perm ↥(Z1 p k Ω K M I) := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  have hTcoe : (T : ↥(Z1 p k Ω K M I) → ↥(Z1 p k Ω K M I)) = g := rfl
  refine ⟨Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I)), Fintype.card_pos_iff.mpr ⟨1⟩, ?_⟩
  intro z
  have hcard : T ^ (Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I))) = 1 := pow_card_eq_one
  have h1 : (T ^ (Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I)))) z = z := by
    rw [hcard]
    rfl
  have h2 : (T ^ (Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I)))) z
      = ((tw1 p k Ω K M I σ H (sigC k Ω σ)) ^
          (Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I)))) z := by
    rw [Equiv.Perm.coe_pow, hTcoe]
    induction (Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I))) with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, pow_succ', Module.End.mul_apply]
  rw [tw1_pow, ← h2, h1]

/-- The partial sums `j ↦ ∑_{i<j} tw1 σ^i β`. -/
def Psi (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) (j : ℕ) : ↥(Z1 p k Ω K M I) :=
  ∑ i ∈ Finset.range j, tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ i) β

@[simp] lemma Psi_zero (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) : Psi p k Ω K M I σ H β 0 = 0 := by
  simp [Psi]

lemma Psi_succ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) (j : ℕ) :
    Psi p k Ω K M I σ H β (j + 1) =
      Psi p k Ω K M I σ H β j + tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ j) β := by
  rw [Psi, Finset.sum_range_succ, Psi]

lemma Psi_add (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) (j m : ℕ) :
    Psi p k Ω K M I σ H β (j + m) =
      Psi p k Ω K M I σ H β j + tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ j)
        (Psi p k Ω K M I σ H β m) := by
  simp only [Psi, Finset.sum_range_add]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tw1_comp, pow_add]

/-- The sum over a full period `p·e` vanishes. -/
lemma Psi_mul_period (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) (e : ℕ)
    (he : ∀ z : ↥(Z1 p k Ω K M I), tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ e) z = z) :
    Psi p k Ω K M I σ H β (p * e) = 0 := by
  have htw : tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ e) = 1 := by
    rw [Module.End.one_eq_id]
    exact LinearMap.ext he
  have h1 : ∀ m : ℕ, Psi p k Ω K M I σ H β (m * e) =
      m • (Psi p k Ω K M I σ H β e) := by
    intro m
    induction m with
    | zero => rw [Nat.zero_mul, zero_smul, Psi_zero]
    | succ m ih =>
        rw [Nat.succ_mul, Psi_add, ih]
        have h2 : tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ (m * e))
            (Psi p k Ω K M I σ H β e) = Psi p k Ω K M I σ H β e := by
          rw [pow_mul' (sigC k Ω σ) m e, tw1_pow, htw, one_pow]
          rfl
        rw [h2, succ_nsmul]
  rw [h1 p, ← Nat.cast_smul_eq_nsmul (ZMod p) p (Psi p k Ω K M I σ H β e),
    ZMod.natCast_self, zero_smul]

/-- Periodicity of the partial sums. -/
lemma Psi_period (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) (e : ℕ)
    (he : ∀ z : ↥(Z1 p k Ω K M I), tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ e) z = z)
    (j : ℕ) :
    Psi p k Ω K M I σ H β (j + p * e) = Psi p k Ω K M I σ H β j := by
  rw [Psi_add, Psi_mul_period p k Ω K M I σ H β e he, map_zero, add_zero]

/-- The partial sums as a function on `ZMod (p·e)`. -/
def PsiZ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) (β : ↥(Z1 p k Ω K M I)) : ZMod (p * e) → ↥(Z1 p k Ω K M I) :=
  fun x => Psi p k Ω K M I σ H β x.val

@[simp] lemma PsiZ_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) (β : ↥(Z1 p k Ω K M I)) (x : ZMod (p * e)) :
    PsiZ p k Ω K M I σ H e β x = Psi p k Ω K M I σ H β x.val := rfl

/-- The crossed homomorphism identity for the partial sums on `ZMod (p·e)`. -/
lemma PsiZ_add (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) [NeZero (p * e)] (β : ↥(Z1 p k Ω K M I))
    (he : ∀ z : ↥(Z1 p k Ω K M I), tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ e) z = z)
    (x y : ZMod (p * e)) :
    PsiZ p k Ω K M I σ H e β (x + y) =
      PsiZ p k Ω K M I σ H e β x
        + tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ x.val)
            (PsiZ p k Ω K M I σ H e β y) := by
  classical
  show Psi p k Ω K M I σ H β (x + y).val =
    Psi p k Ω K M I σ H β x.val
      + tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ x.val) (Psi p k Ω K M I σ H β y.val)
  rw [ZMod.val_add, ← Psi_add]
  rcases Nat.lt_or_ge (x.val + y.val) (p * e) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]
  · have h2 : (x.val + y.val) % (p * e) = x.val + y.val - p * e := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt]
      have := ZMod.val_lt (n := p * e) x
      have := ZMod.val_lt (n := p * e) y
      omega
    have h3 : Psi p k Ω K M I σ H β (x.val + y.val) =
        Psi p k Ω K M I σ H β (x.val + y.val - p * e) := by
      have h1 : x.val + y.val = (x.val + y.val - p * e) + p * e := by
        have := ZMod.val_lt (n := p * e) x
        have := ZMod.val_lt (n := p * e) y
        omega
      conv_lhs => rw [h1]
      rw [Psi_period p k Ω K M I σ H β e he]
    rw [h2, h3]

/-- A continuous homomorphism `C →* Multiplicative (ZMod N)` sending `σ` to `1`. -/
lemma exists_chiC (σ : Ω ≃ₐ[k] Ω) (N : ℕ) (hN : 0 < N)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Ccl k Ω σ) →* Multiplicative (ZMod n),
      Function.Surjective f) :
    ∃ χ : ↥(Ccl k Ω σ) →* Multiplicative (ZMod N),
      Continuous χ ∧ χ (sigC k Ω σ) = Multiplicative.ofAdd 1 :=
  Work.SSGRoute.HSTwoRow.exists_cont_hom_zmod_zpowers k Ω σ N hN
    Work.SSGRoute.HSTwoRow.mem_powSubgroup_all_eq_one hZ

/-- The crossed homomorphism `C → Z1` attached to `β`, `e` and `χ`. -/
def Phi (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) (χ : ↥(Ccl k Ω σ) →* Multiplicative (ZMod (p * e)))
    (β : ↥(Z1 p k Ω K M I)) (γ : ↥(Ccl k Ω σ)) : ↥(Z1 p k Ω K M I) :=
  PsiZ p k Ω K M I σ H e β (Multiplicative.toAdd (χ γ))

@[simp] lemma Phi_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) (χ : ↥(Ccl k Ω σ) →* Multiplicative (ZMod (p * e)))
    (β : ↥(Z1 p k Ω K M I)) (γ : ↥(Ccl k Ω σ)) :
    Phi p k Ω K M I σ H e χ β γ
      = PsiZ p k Ω K M I σ H e β (Multiplicative.toAdd (χ γ)) := rfl

lemma Phi_sigC (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) (h1lt : 1 < p * e)
    (χ : ↥(Ccl k Ω σ) →* Multiplicative (ZMod (p * e)))
    (hχ : χ (sigC k Ω σ) = Multiplicative.ofAdd 1)
    (β : ↥(Z1 p k Ω K M I)) :
    Phi p k Ω K M I σ H e χ β (sigC k Ω σ) = β := by
  haveI : Fact (1 < p * e) := ⟨h1lt⟩
  rw [Phi_apply, hχ, toAdd_ofAdd, PsiZ_apply, ZMod.val_one, Psi, Finset.sum_range_one,
    pow_zero, tw1_one]
  rfl

lemma Phi_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) [NeZero (p * e)] (χ : ↥(Ccl k Ω σ) →* Multiplicative (ZMod (p * e)))
    (β : ↥(Z1 p k Ω K M I)) :
    Phi p k Ω K M I σ H e χ β 1 = 0 := by
  rw [Phi_apply, map_one, toAdd_one, PsiZ_apply, ZMod.val_zero, Psi_zero]

end

end Work.SSGRoute.HSRow

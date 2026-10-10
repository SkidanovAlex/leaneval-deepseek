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
import Submission.Work.SSGRoute.PT.e1a_chain
import Submission.Work.SSGRoute.PT.shapiro_H2_coind
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro: `Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ) ≅ Coind_{Gal(Ω/K)}^{Gal(Ω/k)}(Ωˣ)^n`

For `k` a field with algebraic closure `Ω`, `K/k` a finite Galois subextension and `n : ℕ`, the
`Gal(Ω/k)`-module `homCoindFree k Ω K n = Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ)` with the *conjugation* action

  `(σ · φ) x = σ · φ (M.ρ ((res σ)⁻¹) x)`

is isomorphic to the coinduced module `Coind_{G_K}^Γ ((Ωˣ)^n)` (`Γ = Gal(Ω/k)`,
`G_K = K.fixingSubgroup = Gal(Ω/K) = ker res`), compatibly with the `Γ`-action.  The isomorphism
is the classical Shapiro/Frobenius identification

  `Φ(φ)(γ) i = γ⁻¹ · φ (γ · e_i)`,  `Φ⁻¹(f)(e_{i,g}) = s(g) · f(s(g)) i`,

where `s` is a section of `res k K` (surjective because `Ω` is algebraically closed).

## Instance note

`homCoindFree k Ω K n` is (`@[reducible]`) `M.V →+ Additive Ωˣ`; type class search for `SMul` would
otherwise pick the *pointwise* action on `AddMonoidHom` (`(σ • w) x = σ • w x`).  With the pointwise
action the statement below is **false** (`Γ`-invariants would be `(kˣ)^{n·|G|}` on the left but
`(Kˣ)^n` on the right), so the conjugation action is pinned here with a local instance, exactly as
in `Submission/Work/SSGRoute/PT/homCoind_SES.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute.PT

open CategoryTheory

noncomputable section

variable (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The conjugation action of `Γ = Gal(Ω/k)` on `Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ)`, pinned so that type
class search does not pick the pointwise action on `AddMonoidHom`. -/
def smulConjCoindFree (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] (n : ℕ) :
    SMul (Ω ≃ₐ[k] Ω) (homCoindFree k Ω K n) :=
  ⟨fun σ φ => (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv
      (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (Fin n))).smul σ φ⟩

attribute [local instance 10000] smulConjCoindFree

section Main

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] {n : ℕ}

/-- `ℤ[Gal(K/k)]^n`, the underlying module of `homCoindFree k Ω K n`. -/
abbrev FreeRep (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (n : ℕ) : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
  Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (Fin n)

/-- The basis element `e_{i,g} = δ_i · g` of `ℤ[Gal(K/k)]^n`. -/
def basisV (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (n : ℕ) (i : Fin n) (g : K ≃ₐ[k] K) : (FreeRep k Ω K n).V :=
  Finsupp.single i (MonoidAlgebra.single g 1)

/-- The pinned action is the conjugation action. -/
theorem homCoindFree_smul_apply (σ : Ω ≃ₐ[k] Ω) (w : homCoindFree k Ω K n)
    (x : (FreeRep k Ω K n).V) :
    (σ • w) x = σ • w ((FreeRep k Ω K n).ρ (((SSGRoute.res k K) σ)⁻¹) x) := rfl

/-- The `Gal(K/k)`-action on the basis of `ℤ[Gal(K/k)]^n`. -/
@[simp] theorem ρ_basisV (g : K ≃ₐ[k] K) (i : Fin n) :
    (FreeRep k Ω K n).ρ g (basisV k Ω K n i 1) = basisV k Ω K n i g := by
  show ((Representation.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (Fin n)) g)
      (Finsupp.single i (MonoidAlgebra.single 1 1)) = _
  rw [Representation.free_single_single, mul_one]
  rfl

/-- Composition of the `Gal(K/k)`-action on `ℤ[Gal(K/k)]^n`. -/
theorem ρ_mul_apply (g h : K ≃ₐ[k] K) (x : (FreeRep k Ω K n).V) :
    (FreeRep k Ω K n).ρ g ((FreeRep k Ω K n).ρ h x) = (FreeRep k Ω K n).ρ (g * h) x := by
  rw [Rep.ρ_mul]
  rfl

/-- `K.fixingSubgroup` is the kernel of `res k K`. -/
theorem mem_fixingSubgroup_iff_res_eq_one (u : Ω ≃ₐ[k] Ω) :
    SSGRoute.res k K u = 1 ↔ u ∈ K.fixingSubgroup := by
  rw [show SSGRoute.res k K u = u.restrictNormal K from rfl, AlgEquiv.restrictNormal_eq_one_iff,
    IntermediateField.mem_fixingSubgroup_iff]

/-- Elements of `K.fixingSubgroup` are trivial in `Gal(K/k)`. -/
theorem res_eq_one_of_mem_fixingSubgroup (u : K.fixingSubgroup) :
    SSGRoute.res k K (u : Ω ≃ₐ[k] Ω) = 1 :=
  (mem_fixingSubgroup_iff_res_eq_one (k := k) (Ω := Ω) (K := K) u).mpr u.2

/-- A section of `res k K` (`Ω` algebraically closed). -/
def resSection (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] (g : K ≃ₐ[k] K) :
    Ω ≃ₐ[k] Ω :=
  Classical.choose (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) Ω g)

theorem resSection_spec (g : K ≃ₐ[k] K) :
    SSGRoute.res k K (resSection k Ω K g) = g :=
  Classical.choose_spec (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) Ω g)

/-- Coordinates of a coinduced function: evaluate at the section of `g`, act, and read off
component `i`. -/
def coindCoord (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ)) :
    Fin n → (K ≃ₐ[k] K) → Additive Ωˣ :=
  fun i g => resSection k Ω K g • f (resSection k Ω K g) i

/-- Evaluation of `freeHomEquiv.symm` at a basis vector. -/
theorem freeHomEquiv_symm_basis (h : Fin n → (K ≃ₐ[k] K) → Additive Ωˣ) (i : Fin n)
    (g : K ≃ₐ[k] K) :
    Work.SSGRoute.freeHomEquiv.symm h (basisV k Ω K n i g) = h i g := by
  have h1 := Work.SSGRoute.freeHomEquiv_apply (k := k) (Ω := Ω) (K := K) (ι := Fin n)
    (Work.SSGRoute.freeHomEquiv.symm h) i g
  rw [AddEquiv.apply_symm_apply] at h1
  exact h1.symm

/-! ## The forward map `homCoindFree → Coind` -/

/-- Coordinates of a homomorphism in the coinduced form: `w ↦ (γ ↦ i ↦ γ⁻¹ · w(γ · e_i))`. -/
def toCoindFun (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (n : ℕ) (w : homCoindFree k Ω K n) :
    (Ω ≃ₐ[k] Ω) → (Fin n → Additive Ωˣ) :=
  fun γ i => γ⁻¹ • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1))

theorem toCoindFun_rel (w : homCoindFree k Ω K n) (γ : Ω ≃ₐ[k] Ω) (u : K.fixingSubgroup) :
    toCoindFun k Ω K n w (γ * (u : Ω ≃ₐ[k] Ω)) = u⁻¹ • toCoindFun k Ω K n w γ := by
  funext i
  have h1 : SSGRoute.res k K (γ * (u : Ω ≃ₐ[k] Ω)) = SSGRoute.res k K γ := by
    rw [map_mul, res_eq_one_of_mem_fixingSubgroup (k := k) (Ω := Ω) (K := K) u, mul_one]
  show (γ * (u : Ω ≃ₐ[k] Ω))⁻¹
        • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K (γ * (u : Ω ≃ₐ[k] Ω))) (basisV k Ω K n i 1))
      = (u : Ω ≃ₐ[k] Ω)⁻¹
        • (γ⁻¹ • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1)))
  rw [h1, mul_inv_rev, mul_smul]

/-- The forward map `Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ) → Coind_{G_K}^Γ((Ωˣ)^n)`. -/
def toCoind (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (n : ℕ) (w : homCoindFree k Ω K n) :
    Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ) :=
  ⟨toCoindFun k Ω K n w, fun γ u => toCoindFun_rel (k := k) (Ω := Ω) (K := K) (n := n) w γ u⟩

theorem toCoind_add (w w' : homCoindFree k Ω K n) :
    toCoind k Ω K n (w + w') = toCoind k Ω K n w + toCoind k Ω K n w' := by
  apply Subtype.ext
  funext γ i
  show γ⁻¹ • (w + w') ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1))
      = γ⁻¹ • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1))
        + γ⁻¹ • w' ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1))
  rw [AddMonoidHom.add_apply, smul_add]

theorem toCoind_smul (σ : Ω ≃ₐ[k] Ω) (w : homCoindFree k Ω K n) :
    toCoind k Ω K n (σ • w) = σ • toCoind k Ω K n w := by
  apply Subtype.ext
  funext γ i
  have hL : toCoind k Ω K n (σ • w) γ i
      = (γ⁻¹ * σ) • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K (σ⁻¹ * γ))
          (basisV k Ω K n i 1)) := by
    show γ⁻¹ • (σ • w) ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1)) = _
    rw [homCoindFree_smul_apply, ρ_mul_apply, ← mul_smul]
    congr 1
    rw [← map_inv, ← map_mul]
  have hR : (σ • toCoind k Ω K n w) γ i
      = (γ⁻¹ * σ) • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K (σ⁻¹ * γ))
          (basisV k Ω K n i 1)) := by
    rw [Coind.smul_apply]
    show (σ⁻¹ * γ)⁻¹ • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K (σ⁻¹ * γ))
        (basisV k Ω K n i 1)) = _
    rw [mul_inv_rev, inv_inv]
  rw [hL, hR]

/-! ## The inverse map `Coind → homCoindFree` -/

/-- The inverse map `Coind_{G_K}^Γ((Ωˣ)^n) → Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ)`. -/
def ofCoind (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (n : ℕ) (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ)) :
    homCoindFree k Ω K n :=
  Work.SSGRoute.freeHomEquiv.symm (coindCoord (k := k) (Ω := Ω) (K := K) (n := n) f)

theorem freeHomEquiv_ofCoind (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ)) :
    Work.SSGRoute.freeHomEquiv (ofCoind k Ω K n f) = coindCoord f := by
  show Work.SSGRoute.freeHomEquiv
      (Work.SSGRoute.freeHomEquiv.symm (coindCoord (k := k) (Ω := Ω) (K := K) (n := n) f))
    = coindCoord f
  rw [AddEquiv.apply_symm_apply]

theorem ofCoind_apply_basis (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ))
    (i : Fin n) (g : K ≃ₐ[k] K) :
    ofCoind k Ω K n f (basisV k Ω K n i g) = resSection k Ω K g • f (resSection k Ω K g) i := by
  show Work.SSGRoute.freeHomEquiv.symm (coindCoord (k := k) (Ω := Ω) (K := K) (n := n) f)
      (basisV k Ω K n i g) = resSection k Ω K g • f (resSection k Ω K g) i
  rw [freeHomEquiv_symm_basis]
  rfl

theorem ofCoind_add (f f' : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ)) :
    ofCoind k Ω K n (f + f') = ofCoind k Ω K n f + ofCoind k Ω K n f' := by
  apply Work.SSGRoute.freeHomEquiv.injective
  rw [freeHomEquiv_ofCoind, map_add, freeHomEquiv_ofCoind, freeHomEquiv_ofCoind]
  funext i g
  show resSection k Ω K g • (f (resSection k Ω K g) i + f' (resSection k Ω K g) i)
      = resSection k Ω K g • f (resSection k Ω K g) i
        + resSection k Ω K g • f' (resSection k Ω K g) i
  rw [smul_add]

/-! ## The two inverse laws -/

/-- `γ' · f γ'` only depends on `res γ'`. -/
theorem coind_smul_self_eq (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ))
    (γ : Ω ≃ₐ[k] Ω) (u : K.fixingSubgroup) :
    ((γ * (u : Ω ≃ₐ[k] Ω)) • f (γ * (u : Ω ≃ₐ[k] Ω))) = γ • f γ := by
  rw [Coind.coe_mul]
  show (γ * (u : Ω ≃ₐ[k] Ω)) • ((u : Ω ≃ₐ[k] Ω)⁻¹ • f γ) = γ • f γ
  have hcoe : (γ * (u : Ω ≃ₐ[k] Ω)) * ((u : Ω ≃ₐ[k] Ω)⁻¹) = γ := by
    rw [mul_assoc, ← Subgroup.coe_inv, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      mul_one]
  rw [← mul_smul, hcoe]

theorem coind_smul_self_lift_eq (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ))
    (γ γ' : Ω ≃ₐ[k] Ω) (h : SSGRoute.res k K γ' = SSGRoute.res k K γ) :
    γ' • f γ' = γ • f γ := by
  have hu : γ⁻¹ * γ' ∈ K.fixingSubgroup := by
    rw [← mem_fixingSubgroup_iff_res_eq_one, map_mul, map_inv, h, inv_mul_cancel]
  have hγγ' : γ * (⟨γ⁻¹ * γ', hu⟩ : K.fixingSubgroup) = γ' := by
    show γ * (γ⁻¹ * γ') = γ'
    group
  rw [← hγγ']
  exact coind_smul_self_eq (k := k) (Ω := Ω) (K := K) (n := n) f γ ⟨γ⁻¹ * γ', hu⟩

theorem coind_smul_self_lift_apply (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ))
    (γ γ' : Ω ≃ₐ[k] Ω) (h : SSGRoute.res k K γ' = SSGRoute.res k K γ) (i : Fin n) :
    γ' • f γ' i = γ • f γ i :=
  congrFun (coind_smul_self_lift_eq (k := k) (Ω := Ω) (K := K) (n := n) f γ γ' h) i

theorem ofCoind_toCoind (w : homCoindFree k Ω K n) : ofCoind k Ω K n (toCoind k Ω K n w) = w := by
  apply Work.SSGRoute.freeHomEquiv.injective
  rw [freeHomEquiv_ofCoind]
  funext i g
  show resSection k Ω K g • toCoind k Ω K n w (resSection k Ω K g) i
      = Work.SSGRoute.freeHomEquiv w i g
  rw [show toCoind k Ω K n w (resSection k Ω K g) i
      = (resSection k Ω K g)⁻¹ • w ((FreeRep k Ω K n).ρ (SSGRoute.res k K (resSection k Ω K g))
          (basisV k Ω K n i 1)) from rfl,
    resSection_spec, ← mul_smul, mul_inv_cancel, one_smul, ρ_basisV,
    Work.SSGRoute.freeHomEquiv_apply]
  rfl

theorem toCoind_ofCoind (f : Coind (Ω ≃ₐ[k] Ω) K.fixingSubgroup (Fin n → Additive Ωˣ)) :
    toCoind k Ω K n (ofCoind k Ω K n f) = f := by
  apply Subtype.ext
  funext γ i
  show γ⁻¹ • ofCoind k Ω K n f ((FreeRep k Ω K n).ρ (SSGRoute.res k K γ) (basisV k Ω K n i 1))
      = f γ i
  rw [ρ_basisV, ofCoind_apply_basis,
    coind_smul_self_lift_apply (k := k) (Ω := Ω) (K := K) (n := n) f γ
      (resSection k Ω K (SSGRoute.res k K γ))
      (resSection_spec (k := k) (Ω := Ω) (K := K) (SSGRoute.res k K γ)) i,
    ← mul_smul, inv_mul_cancel, one_smul]

end Main

theorem homCoindFree_coind_iso (k Ω : Type) [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (n : ℕ) :
    ∃ Φ : Work.SSGRoute.PT.homCoindFree k Ω K n ≃+
        Work.SSGRoute.PT.Coind (Ω ≃ₐ[k] Ω) (K.fixingSubgroup) (Fin n → Additive Ωˣ),
      ∀ (σ : Ω ≃ₐ[k] Ω) (w : Work.SSGRoute.PT.homCoindFree k Ω K n),
        Φ (σ • w) = σ • Φ w := by
  refine ⟨{ toFun := toCoind k Ω K n
            invFun := ofCoind k Ω K n
            left_inv := fun w => ofCoind_toCoind (k := k) (Ω := Ω) (K := K) (n := n) w
            right_inv := fun f => toCoind_ofCoind (k := k) (Ω := Ω) (K := K) (n := n) f
            map_add' := fun w w' => toCoind_add (k := k) (Ω := Ω) (K := K) (n := n) w w' }, ?_⟩
  intro σ w
  exact toCoind_smul (k := k) (Ω := Ω) (K := K) (n := n) σ w

/-- **The `IsEquivariant` form** of `homCoindFree_coind_iso`: the Shapiro isomorphism is
`Gal(Ω/k)`-equivariant in the sense of `Work.GroupCohomology.IsEquivariant` (the shape consumed by
the `E1a` computation). -/
theorem homCoindFree_coind_iso_conj (k Ω : Type) [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] (n : ℕ) :
    ∃ Zc : Work.SSGRoute.PT.homCoindFree k Ω K n ≃+
        Work.SSGRoute.PT.Coind (Ω ≃ₐ[k] Ω) (K.fixingSubgroup) (Fin n → Additive Ωˣ),
      Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Zc.toAddMonoidHom := by
  obtain ⟨Φ, hΦ⟩ := homCoindFree_coind_iso (k := k) (Ω := Ω) (K := K) (n := n)
  exact ⟨Φ, hΦ⟩

end

end Work.SSGRoute.PT

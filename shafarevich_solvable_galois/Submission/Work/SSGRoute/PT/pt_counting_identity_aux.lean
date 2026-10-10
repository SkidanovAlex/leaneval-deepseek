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
import Submission.Work.SSGRoute.PT.pt_canonical_assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for `Work.SSGRoute.PT.pt_selmer_counting_identity`

This module holds the auxiliary lemmas that the *counting* lane
(`Submission/Work/SSGRoute/PT/pt_selmer_counting_identity.lean`) needs and that cannot be quoted
from `Submission/Work/SSGRoute/PT/pt_counting_identity_h1.lean` (that module imports the counting
lane's own file, so importing it back would be a cycle):

* `PT.natCard_annihilator_mul` — the pure linear-algebra half of the counting identity
  (`|W^⊥| · |W| = |P|` for a perfect pairing), and its additive form
  `PT.CountAux.natCard_annihilator_mul_additive`, which is the form in which the product of the
  local Tate pairings is available;
* `CountAux.primalClassSet_orthogonal_dualClassSet` — the *proved* reciprocity inclusion
  `V ⊆ W^⊥` at the level of the class sets (`primalClassSet`, `dualClassSet`), i.e. the
  representative-level reciprocity law `PT.pt_orthogonality_of_realizable` pushed through
  `PT.productFormFun_primalClassOf`.  It is the half of the middle exactness that *is* available;
  its converse `W^⊥ ⊆ V` is the arithmetic input of the counting identity (`G1⁺`'s clause (8)).

Everything here is stated in the vocabulary of `PT/pt_counting_assembly.lean` and
`PT/pt_canonical_assembly.lean` and rests on no unproved node.  (This module deliberately does
*not* import `PT/canonical_localPairing_reciprocity_converse.lean`: the `G1⁺` node is imported
only by the counting lane itself, so that everything above it can be built without it.)
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute.PT

noncomputable section

/-- **Cardinality form of the annihilator identity for a perfect pairing.**
For a pairing `β : P →ₗ Q →ₗ 𝔽_p` which is non-degenerate in both variables and a subspace
`W ≤ Q`, the "annotator" `{x : P // ∀ y ∈ W, β x y = 0}` of `W` satisfies
`|W^⊥| · |W| = |P|`.  This is the pure-linear-algebra half of the Poitou–Tate counting
identity. -/
theorem natCard_annihilator_mul {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P →ₗ[ZMod p] Q →ₗ[ZMod p] ZMod p)
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hndR : ∀ y : Q, (∀ x : P, β x y = 0) → y = 0)
    (W : Submodule (ZMod p) Q) :
    Nat.card {x : P // ∀ y ∈ W, β x y = 0} * Nat.card W = Nat.card P := by
  classical
  haveI hPf : Module.Finite (ZMod p) P := Module.Finite.of_finite
  haveI hQf : Module.Finite (ZMod p) Q := Module.Finite.of_finite
  haveI hWf : Module.Finite (ZMod p) W := Module.Finite.of_finite
  have hinjΦ : Function.Injective β := by
    intro x y hxy
    have hz : β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : ∀ z : Q, β (x - y) z = 0 := fun z => by rw [hz]; rfl
    have h1 : x - y = 0 := hndL (x - y) h0
    rwa [sub_eq_zero] at h1
  have hinjΨ : Function.Injective (LinearMap.flip β) := by
    intro x y hxy
    have hz : LinearMap.flip β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : ∀ z : P, β z (x - y) = 0 := by
      intro z
      have h1 := congrArg (fun (f : P →ₗ[ZMod p] ZMod p) => f z) hz
      simpa using h1
    have h1 : x - y = 0 := hndR (x - y) h0
    rwa [sub_eq_zero] at h1
  have hPQ : Module.finrank (ZMod p) P = Module.finrank (ZMod p) Q := by
    have h1 : Module.finrank (ZMod p) P ≤ Module.finrank (ZMod p) Q := by
      have h := LinearMap.finrank_le_finrank_of_injective (R := ZMod p)
        (M := P) (M' := Module.Dual (ZMod p) Q) hinjΦ
      rwa [Subspace.dual_finrank_eq] at h
    have h2 : Module.finrank (ZMod p) Q ≤ Module.finrank (ZMod p) P := by
      have h := LinearMap.finrank_le_finrank_of_injective (R := ZMod p)
        (M := Q) (M' := Module.Dual (ZMod p) P) hinjΨ
      rwa [Subspace.dual_finrank_eq] at h
    omega
  have hmem : ∀ x : P, (∀ y ∈ W, β x y = 0) ↔ x ∈ (Submodule.dualAnnihilator W).comap β := by
    intro x
    rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  have hann : Module.finrank (ZMod p) (Submodule.dualAnnihilator W)
      = Module.finrank (ZMod p) Q - Module.finrank (ZMod p) W := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    omega
  have hPQ' : Module.finrank (ZMod p) P = Module.finrank (ZMod p) (Module.Dual (ZMod p) Q) := by
    rw [Subspace.dual_finrank_eq]; exact hPQ
  have hcomap : Module.finrank (ZMod p) ((Submodule.dualAnnihilator W).comap β)
      = Module.finrank (ZMod p) (Submodule.dualAnnihilator W) := by
    let f : ((Submodule.dualAnnihilator W).comap β) →ₗ[ZMod p]
        Submodule.dualAnnihilator W :=
      { toFun := fun x => ⟨β x.1, x.2⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun c x => by ext; simp }
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        have h1 : β x.1 = β y.1 := congrArg Subtype.val hxy
        exact Subtype.ext (hinjΦ h1)
      · rintro ⟨φ, hφ⟩
        obtain ⟨x, rfl⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hPQ').mp
          hinjΦ φ
        exact ⟨⟨x, by rw [Submodule.mem_comap]; exact hφ⟩, Subtype.ext rfl⟩
    exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective f hf)
  have hfin : Module.finrank (ZMod p) ↥((Submodule.dualAnnihilator W).comap β)
      = Module.finrank (ZMod p) P - Module.finrank (ZMod p) W := by
    rw [hcomap, hann]; omega
  have hcard1 : Nat.card {x : P // ∀ y ∈ W, β x y = 0}
      = p ^ (Module.finrank (ZMod p) P - Module.finrank (ZMod p) W) := by
    have h1 : Nat.card {x : P // ∀ y ∈ W, β x y = 0}
        = Nat.card ↥((Submodule.dualAnnihilator W).comap β) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => hmem x))
    rw [h1, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, hfin]
  have hcard2 : Nat.card W = p ^ Module.finrank (ZMod p) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hcard3 : Nat.card P = p ^ Module.finrank (ZMod p) P := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hle : Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) P := by
    have h1 : Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) Q := Submodule.finrank_le W
    omega
  rw [hcard1, hcard2, hcard3, ← pow_add, Nat.sub_add_cancel hle]

namespace CountAux

set_option maxHeartbeats 1000000 in
/-- **Cardinality form of the annihilator identity for an additively given perfect pairing.**

`natCard_annihilator_mul` above is stated for a `ZMod p`-*bilinear* form; the product form of the
local Tate pairings (`Work.SSGRoute.PT.productFormFun`) is only known to be *additive* in each
variable (`productFormFun_add_left` / `productFormFun_add_right`).  Since the scalar action of
`ZMod p` on a `ZMod p`-module is determined by the additive structure, additivity in each variable
upgrades to bilinearity, and the counting lemma applies verbatim. -/
theorem natCard_annihilator_mul_additive {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P → Q → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hndR : ∀ y : Q, (∀ x : P, β x y = 0) → y = 0)
    (W : Submodule (ZMod p) Q) :
    Nat.card {x : P // ∀ y ∈ W, β x y = 0} * Nat.card W = Nat.card P := by
  classical
  have hzeroR : ∀ x : P, β x 0 = 0 := by
    intro x
    have h : β x 0 + β x 0 = β x 0 + 0 := by
      rw [← haddR x 0 0]; simp
    exact add_left_cancel h
  have hzeroL : ∀ y : Q, β 0 y = 0 := by
    intro y
    have h : β 0 y + β 0 y = β 0 y + 0 := by
      rw [← haddL 0 0 y]; simp
    exact add_left_cancel h
  have hnatL : ∀ (n : ℕ) (x : P) (y : Q), β (n • x) y = n • β x y := by
    intro n
    induction n with
    | zero => intro x y; rw [zero_nsmul, hzeroL, zero_nsmul]
    | succ n ih =>
      intro x y
      rw [succ_nsmul, haddL, ih x y, succ_nsmul]
  have hnatR : ∀ (n : ℕ) (x : P) (y : Q), β x (n • y) = n • β x y := by
    intro n
    induction n with
    | zero => intro x y; rw [zero_nsmul, hzeroR, zero_nsmul]
    | succ n ih =>
      intro x y
      rw [succ_nsmul, haddR, ih x y, succ_nsmul]
  have hsmulL : ∀ (c : ZMod p) (x : P) (y : Q), β (c • x) y = c * β x y := by
    intro c x y
    have h1 : β ((c.val : ZMod p) • x) y = (c.val : ZMod p) * β x y := by
      rw [Nat.cast_smul_eq_nsmul (ZMod p), hnatL, nsmul_eq_mul]
    rwa [ZMod.natCast_zmod_val] at h1
  have hsmulR : ∀ (c : ZMod p) (x : P) (y : Q), β x (c • y) = c * β x y := by
    intro c x y
    have h1 : β x ((c.val : ZMod p) • y) = (c.val : ZMod p) * β x y := by
      rw [Nat.cast_smul_eq_nsmul (ZMod p), hnatR, nsmul_eq_mul]
    rwa [ZMod.natCast_zmod_val] at h1
  let f : P → Q →ₗ[ZMod p] ZMod p := fun x =>
    { toFun := β x
      map_add' := fun y y' => haddR x y y'
      map_smul' := fun c y => by
        show β x (c • y) = c • β x y
        rw [hsmulR c x y, smul_eq_mul] }
  let βlin : P →ₗ[ZMod p] Q →ₗ[ZMod p] ZMod p :=
    { toFun := f
      map_add' := fun x x' => by
        ext y
        show β (x + x') y = β x y + β x' y
        rw [haddL x x' y]
      map_smul' := fun c x => by
        ext y
        show β (c • x) y = c • β x y
        rw [hsmulL c x y, smul_eq_mul] }
  exact natCard_annihilator_mul (p := p) βlin hndL hndR W

end CountAux

end

open scoped TensorProduct Pointwise

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

local instance instCountAuxDualAC :
    AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance
local instance instCountAuxDualMod :
    Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance
local instance instCountAuxDualDMA :
    DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance instCountAuxDualSMC :
    SMulCommClass (K ≃ₐ[k] K) (ZMod p)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance

set_option maxHeartbeats 2000000 in
/-- **The reciprocity inclusion `V ⊆ W^⊥` at the level of the class sets.**

For local data `pair` satisfying the local axioms (1)–(5) at every place of `S ∪ C` and the
reciprocity law (7) `hrec`, every *realizable* class `x` (an element of `primalClassSet`) is
orthogonal, under the product form of the descended local pairings, to every relaxed dual Selmer
class `y` (an element of `dualClassSet`).

This is the representative-level reciprocity law
`Work.SSGRoute.PT.pt_orthogonality_of_realizable` (applied through
`Work.SSGRoute.PT.productFormFun_primalClassOf`, which identifies the class-level product form with
the sum of the local pairings on representatives).  The descended pairing is
`Work.SSGRoute.PT.localPairingFun pair hloc`, whose agreement with `pair` on locally constant
cocycles is `Work.SSGRoute.PT.localPairingFun_toClass`. -/
theorem CountAux.primalClassSet_orthogonal_dualClassSet
    (hKN : K ≤ N)
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
        ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 →
      ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hloc : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), IsLocalGroup k Ω H →
      LocalAxioms (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair H)
    (hrec : Recip (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair) :
    ∀ x : primalClasses p k Ω K M S C,
      x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
          (C := C) →
      ∀ y : primalClasses p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C,
        y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
            (S := S) (C := C) →
        productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C)
          (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc)
          x y = 0 := by
  classical
  intro x hx y hy
  rw [mem_primalClassSet_iff (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
    (M := M) (S := S) (C := C) hCinv x] at hx
  obtain ⟨α', β', ε, hcls, hε1, hε2, hεα', hεβ', hεunr⟩ := hx
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hy
  have hby : dualClassMap (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S)
      (C := C) b.1 = y := hb
  rw [← hby, ← hcls]
  have hεmem : ε ∈ primalSelmer p k Ω K N M S := ⟨hε1, hε2, hεunr⟩
  have hεα'lc : ∀ A ∈ S, (fun σ => ε σ - α' A σ) ∈
      lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
    fun A hA => coboundaries_le_lcCocycles p k Ω K M (SSGRoute.decomp k A)
      ((mem_coboundaries p k Ω K M (SSGRoute.decomp k A) _).mpr (hεα' A hA))
  have hεβ'lc : ∀ c ∈ C, (fun σ => ε σ - β' c σ) ∈
      lcCocycles p k Ω K M (Subgroup.zpowers c) :=
    fun c hc => coboundaries_le_lcCocycles p k Ω K M (Subgroup.zpowers c)
      ((mem_coboundaries p k Ω K M (Subgroup.zpowers c) _).mpr (hεβ' c hc))
  have hα'lc : ∀ A ∈ S, α' A ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) := by
    intro A hA
    have hεA : ε ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
      ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hε1, isLocConstOn_mono le_top hε2⟩
    have heq : α' A = ε - (fun σ => ε σ - α' A σ) := by
      ext σ; simp only [Pi.sub_apply]; abel
    rw [heq]
    exact Submodule.sub_mem _ hεA (hεα'lc A hA)
  have hβ'lc : ∀ c ∈ C, β' c ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) := by
    intro c hc
    have hεc : ε ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) :=
      ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hε1, isLocConstOn_mono le_top hε2⟩
    have heq : β' c = ε - (fun σ => ε σ - β' c σ) := by
      ext σ; simp only [Pi.sub_apply]; abel
    rw [heq]
    exact Submodule.sub_mem _ hεc (hεβ'lc c hc)
  -- the descended pairing agrees with `pair` on locally constant cocycles
  have hB : ∀ A ∈ S, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) →
      b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (SSGRoute.decomp k A) →
      localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc
        (SSGRoute.decomp k A) (toClass p k Ω K M (SSGRoute.decomp k A) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (SSGRoute.decomp k A) b) = pair (SSGRoute.decomp k A) a b :=
    fun A hA => localPairingFun_toClass (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc (Or.inl ⟨A, hSfin A hA, rfl⟩)
  have hBc : ∀ c ∈ C, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) →
      b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Subgroup.zpowers c) →
      localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc
        (Subgroup.zpowers c) (toClass p k Ω K M (Subgroup.zpowers c) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Subgroup.zpowers c) b) = pair (Subgroup.zpowers c) a b :=
    fun c hc => localPairingFun_toClass (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc (Or.inr ⟨c, hCinv c hc, rfl⟩)
  obtain ⟨S', hS'sub, hS'fin, hS'disj, hS'good, hS'cob⟩ :=
    exists_reciprocal_set (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
      (T := T) (M := M) (S := S) hSfin hSdisj hSram ε hεmem b.1 b.2
  have hzero : ∑ A ∈ S, pair (SSGRoute.decomp k A) (α' A) b.1 +
      ∑ c ∈ C, pair (Subgroup.zpowers c) (β' c) b.1 = 0 :=
    pt_orthogonality_of_realizable (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc hrec S hSfin C α' β' ε ⟨hε1, hε2⟩
      (fun A hA => hα'lc A hA) hεα' (fun A hA => hεα'lc A hA)
      (fun c hc => (hβ'lc c hc).1) hεβ' (fun c hc => hεβ'lc c hc)
      b.1 ⟨b.2.1, b.2.2.1⟩ S' hS'sub hS'fin hS'disj hS'good hS'cob hCinv hC hCdisj
  rw [productFormFun_primalClassOf (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T)
    (M := M) (S := S) (C := C) pair
    (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc)
    hB hBc α' β' hα'lc hβ'lc b.1 b.2,
    Finset.sum_attach S (fun A => pair (SSGRoute.decomp k A) (α' A) b.1),
    Finset.sum_attach C (fun c => pair (Subgroup.zpowers c) (β' c) b.1)]
  exact hzero

end

end Work.SSGRoute.PT

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
import Submission.Work.SSGRoute.LTDArch.Defs
import Submission.Work.SSGRoute.PTembedding.localKummer_base
import Submission.Work.SSGRoute.PTembedding.mup_kummer_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclotomic coefficient module `μ_p ⊆ Ω` and its identification with `DualMod p T`
-/

open SSGRoute
open Work.SSGRoute

namespace Work.SSGRoute.PTembedding
namespace MupCard

noncomputable section

set_option linter.style.haveILetI false

/-! ## Rank-one `𝔽_p[G]`-modules and the scalar of the action -/

section RankOne

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {T : Type} [AddCommGroup T]
  [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T]

omit [SMulCommClass G (ZMod p) T] in
/-- The chosen generator `Ach.t0 p T h` is transported by `g` to a scalar multiple of itself. -/
theorem exists_smul_t0_eq (h : Module.finrank (ZMod p) T = 1) (g : G) :
    ∃ c : ZMod p, g • Ach.t0 p T h = c • Ach.t0 p T h := by
  refine ⟨(Ach.rankOneEquiv p T h).symm (g • Ach.t0 p T h), ?_⟩
  have ht : Ach.t0 p T h = Ach.rankOneEquiv p T h 1 := rfl
  rw [ht, ← LinearEquiv.map_smul, smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply]

/-- The scalar by which `g` acts on the chosen generator. -/
noncomputable def rankOneScalar (h : Module.finrank (ZMod p) T = 1) (g : G) : ZMod p :=
  Classical.choose (exists_smul_t0_eq h g)

theorem rankOneScalar_spec (h : Module.finrank (ZMod p) T = 1) (g : G) :
    g • Ach.t0 p T h = rankOneScalar h g • Ach.t0 p T h :=
  Classical.choose_spec (exists_smul_t0_eq h g)

theorem rankOneScalar_ne_zero (h : Module.finrank (ZMod p) T = 1) (g : G) :
    rankOneScalar h g ≠ 0 := by
  intro h0
  have h2 := rankOneScalar_spec h g
  rw [h0, zero_smul] at h2
  have h3 : Ach.t0 p T h = 0 := by
    have hh := congrArg (fun x => g⁻¹ • x) h2
    rwa [smul_zero, inv_smul_smul] at hh
  exact Ach.t0_ne_zero p T h h3

/-- The dual action on `Ach.coord p T h` is by the inverse scalar. -/
theorem smul_coord_eq_inv_smul (h : Module.finrank (ZMod p) T = 1) (g : G) :
    g • Ach.coord p T h = (rankOneScalar h g)⁻¹ • Ach.coord p T h := by
  have hc : rankOneScalar h g ≠ 0 := rankOneScalar_ne_zero h g
  have hgt : g • Ach.t0 p T h = rankOneScalar h g • Ach.t0 p T h := rankOneScalar_spec h g
  have hsm : rankOneScalar h g • (g⁻¹ • Ach.t0 p T h) = Ach.t0 p T h := by
    calc rankOneScalar h g • (g⁻¹ • Ach.t0 p T h)
        = g⁻¹ • (rankOneScalar h g • Ach.t0 p T h) :=
          (smul_comm g⁻¹ (rankOneScalar h g) (Ach.t0 p T h)).symm
      _ = g⁻¹ • (g • Ach.t0 p T h) := by rw [← hgt]
      _ = Ach.t0 p T h := inv_smul_smul g (Ach.t0 p T h)
  have hinv : g⁻¹ • Ach.t0 p T h = (rankOneScalar h g)⁻¹ • Ach.t0 p T h := by
    have h2 := congrArg (fun x => (rankOneScalar h g)⁻¹ • x) hsm
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
    exact h2
  ext s
  have hs : g⁻¹ • s = (rankOneScalar h g)⁻¹ • s := by
    have e1 : s = (Ach.coord p T h s) • Ach.t0 p T h := (Ach.smul_coord_t0 p T h s).symm
    conv_lhs => rw [e1]
    conv_rhs => rw [e1]
    rw [smul_comm, hinv, smul_smul, smul_smul, mul_comm]
  rw [DualMod.dualSMul_apply, hs, map_smul, LinearMap.smul_apply]

end RankOne

/-! ## The cyclotomic action on `T` and on `DualMod p T` -/

section CyclotomicAction

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : Ω} {T : Type} [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- If `g ∈ Gal(K/k)` maps the primitive `p`-th root of unity `ζ ∈ K` to `ζ^m`, then
`(m : ZMod p) • (g • t) = t` for every `t : T`. -/
theorem nsmul_smul_eq_of_smul_zeta_eq_pow (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (g : K ≃ₐ[k] K) (m : ℕ) (hm : g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m) :
    ∀ t : T, (m : ZMod p) • (g • t) = t := by
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := Ω) g
  have hσζ : σ • ζ = ζ ^ m := by
    have h2 : ((AlgEquiv.restrictNormalHom K σ) (⟨ζ, hζK⟩ : K) : Ω) = σ • ζ := by
      rw [AlgEquiv.smul_def]
      exact AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) K σ (⟨ζ, hζK⟩ : K)
    have h4 : (g (⟨ζ, hζK⟩ : K) : Ω) = ζ ^ m := by
      rw [← AlgEquiv.smul_def, hm, IntermediateField.coe_pow]
    rw [← h2, hσ, h4]
  intro t
  have h := hT.2 σ m hσζ t
  have hres : (SSGRoute.res k K) σ = g := hσ
  rw [hres] at h
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) m (g • t)] at h
  exact h

/-- **The action on `T` is the inverse of the cyclotomic character.** -/
theorem smul_eq_inv_of_smul_zeta_eq_pow (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (g : K ≃ₐ[k] K) (m : ℕ) (hm : g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m) :
    ∀ t : T, g • t = ((m : ZMod p))⁻¹ • t := by
  have hkey := nsmul_smul_eq_of_smul_zeta_eq_pow hζK hT g m hm
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro h0
    have h : Ach.t0 p T hT.1 = 0 := by
      have h1 := hkey (Ach.t0 p T hT.1)
      rw [h0, zero_smul] at h1
      exact h1.symm
    exact Ach.t0_ne_zero p T hT.1 h
  intro t
  calc g • t = ((m : ZMod p))⁻¹ • ((m : ZMod p) • (g • t)) := by
        rw [inv_smul_smul₀ hm0]
    _ = ((m : ZMod p))⁻¹ • t := by rw [hkey t]

/-- **`g` acts on `DualMod p T` by the cyclotomic character.** -/
theorem dualMod_smul_eq (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (g : K ≃ₐ[k] K) (m : ℕ) (hm : g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m)
    (φ : Work.SSGRoute.DualMod p T) :
    g • φ = (m : ZMod p) • φ := by
  have hkey := nsmul_smul_eq_of_smul_zeta_eq_pow hζK hT g m hm
  ext t
  have h1 : g⁻¹ • t = (m : ZMod p) • t := by
    have h := hkey (g⁻¹ • t)
    rw [smul_inv_smul] at h
    exact h.symm
  rw [DualMod.dualSMul_apply, LinearMap.smul_apply, h1, map_smul, smul_eq_mul]

end CyclotomicAction

/-! ## `μ_p ⊆ K` as an `𝔽_p`-module -/

section MuAdd

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- `μ_p ⊆ K` as an additive group. -/
abbrev MuAdd (p : ℕ) (K : IntermediateField k Ω) : Type := Additive (rootsOfUnity p K)

theorem toMul_nsmul {G : Type*} [Monoid G] (n : ℕ) (x : Additive G) :
    Additive.toMul (n • x) = Additive.toMul x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; rfl
  | succ n ih => rw [succ_nsmul, toMul_add, ih, pow_succ]

theorem ofMul_nsmul {G : Type*} [Monoid G] (n : ℕ) (x : G) :
    n • (Additive.ofMul x) = Additive.ofMul (x ^ n) := by
  apply Additive.toMul.injective
  show Additive.toMul (n • Additive.ofMul x) = Additive.toMul (Additive.ofMul (x ^ n))
  rw [toMul_nsmul (G := G) n (Additive.ofMul x)]
  rfl

theorem smul_nsmul_comm {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    (g : G) (n : ℕ) (x : M) : g • (n • x) = n • (g • x) := by
  induction n with
  | zero => rw [zero_nsmul, smul_zero, zero_nsmul]
  | succ n ih => rw [succ_nsmul, smul_add, ih, succ_nsmul]

theorem nsmulMuAdd_eq_zero (K : IntermediateField k Ω) (x : MuAdd p K) : p • x = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  show (Additive.toMul x : rootsOfUnity p K) ^ p = 1
  apply Subtype.ext
  show ((Additive.toMul x : rootsOfUnity p K) : Kˣ) ^ p = 1
  exact (mem_rootsOfUnity p ((Additive.toMul x : rootsOfUnity p K) : Kˣ)).mp (Additive.toMul x).2

noncomputable instance instModuleMuAdd (K : IntermediateField k Ω) : Module (ZMod p) (MuAdd p K) :=
  AddCommGroup.zmodModule (nsmulMuAdd_eq_zero (p := p) K)

theorem zmod_smul_eq_nsmul_val {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (r : ZMod p) (m : M) : r • m = r.val • m :=
  Work.CohomologicalShrinking.naturalAlpha.psiLin_zmod_smul_eq_nsmul p r m

noncomputable instance instSMulCommClassMuAdd (K : IntermediateField k Ω) :
    SMulCommClass (K ≃ₐ[k] K) (ZMod p) (MuAdd p K) where
  smul_comm g c x := by
    rw [zmod_smul_eq_nsmul_val (p := p) c x, zmod_smul_eq_nsmul_val (p := p) c (g • x),
      smul_nsmul_comm]

end MuAdd

/-! ## The generator of `μ_p ⊆ K`, its cyclotomic structure -/

section MuCyclic

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
  {K : IntermediateField k Ω}

/-- The unit of `K` determined by the primitive root `ζ ∈ K`. -/
noncomputable def zetaUnit (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) : Kˣ :=
  Units.mk0 (⟨ζ, hζK⟩ : K)
    (fun h => hζ.ne_zero (Fact.out : p.Prime).ne_zero (by simpa using congrArg Subtype.val h))

@[simp] theorem zetaUnit_val (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    ((zetaUnit (p := p) ζ hζ hζK : Kˣ) : K) = ⟨ζ, hζK⟩ := rfl

theorem zetaUnit_pow (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    zetaUnit (p := p) ζ hζ hζK ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, zetaUnit_val, Units.val_one]
  exact Subtype.ext (by rw [IntermediateField.coe_pow]; exact hζ.pow_eq_one)

theorem zetaUnit_ne_one (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    zetaUnit (p := p) ζ hζ hζK ≠ 1 := by
  intro h
  apply hζ.ne_one (Fact.out : p.Prime).one_lt
  have h2 : ((zetaUnit (p := p) ζ hζ hζK : Kˣ) : K) = (1 : K) := by rw [h]; rfl
  rw [zetaUnit_val] at h2
  exact congrArg Subtype.val h2

/-- The element `ζ` of `rootsOfUnity p K`. -/
noncomputable def zrou (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) : rootsOfUnity p K :=
  ⟨zetaUnit (p := p) ζ hζ hζK, (mem_rootsOfUnity p _).mpr (zetaUnit_pow ζ hζ hζK)⟩

@[simp] theorem zrou_coe (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    ((zrou (p := p) ζ hζ hζK : rootsOfUnity p K) : Kˣ) = zetaUnit (p := p) ζ hζ hζK := rfl

/-- The chosen `𝔽_p`-generator of `μ_p ⊆ K`: the class of the primitive root `ζ`. -/
noncomputable def zetaGen (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) : MuAdd p K :=
  Additive.ofMul (zrou (p := p) ζ hζ hζK)

@[simp] theorem zetaGen_eq (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    zetaGen (p := p) ζ hζ hζK = Additive.ofMul (zrou (p := p) ζ hζ hζK) := rfl

theorem zetaGen_ne_zero (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    zetaGen (p := p) ζ hζ hζK ≠ 0 := by
  intro h
  have h1 : zrou (p := p) ζ hζ hζK = 1 := by
    simpa [zetaGen_eq] using congrArg Additive.toMul h
  exact zetaUnit_ne_one ζ hζ hζK (by simpa [zrou] using Subtype.ext_iff.mp h1)

/-- `g` maps the primitive root `ζ ∈ K` to a power of itself. -/
theorem exists_smul_zeta_eq_pow (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (g : K ≃ₐ[k] K) :
    ∃ m : ℕ, g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m := by
  have hx : (⟨ζ, hζK⟩ : K) ^ p = 1 :=
    Subtype.ext (by rw [IntermediateField.coe_pow]; exact hζ.pow_eq_one)
  have hpow : ((g (⟨ζ, hζK⟩ : K) : K) : Ω) ^ p = 1 := by
    rw [← IntermediateField.coe_pow, ← map_pow, hx, map_one]
    rfl
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hpow
  refine ⟨i, ?_⟩
  rw [AlgEquiv.smul_def]
  apply Subtype.ext
  rw [IntermediateField.coe_pow]
  exact hi.symm

@[simp] theorem toMul_smul_muAdd (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (g : K ≃ₐ[k] K) (a : MuAdd p K) :
    Additive.toMul (g • a) = MupKummer.muMapOfField k K p g (Additive.toMul a) := rfl

theorem nsmul_zetaGen_toMul (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (n : ℕ) :
    Additive.toMul (n • zetaGen (p := p) ζ hζ hζK) = (zrou (p := p) ζ hζ hζK) ^ n := by
  rw [zetaGen_eq, toMul_nsmul]
  rfl

theorem zmod_smul_zetaGen_toMul (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (c : ZMod p) :
    Additive.toMul (c • zetaGen (p := p) ζ hζ hζK)
      = (zrou (p := p) ζ hζ hζK) ^ c.val := by
  rw [zmod_smul_eq_nsmul_val, nsmul_zetaGen_toMul]

theorem smul_zetaGen_toMul (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (g : K ≃ₐ[k] K) (m : ℕ) (hm : g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m) :
    Additive.toMul (g • zetaGen (p := p) ζ hζ hζK) = (zrou (p := p) ζ hζ hζK) ^ m := by
  rw [zetaGen_eq]
  show MupKummer.muMapOfField k K p g (zrou (p := p) ζ hζ hζK) = (zrou (p := p) ζ hζ hζK) ^ m
  apply Subtype.ext
  rw [MupKummer.muMapOfField_coe, SubmonoidClass.coe_pow, zrou_coe]
  apply Units.ext
  rw [Work.SSGRoute.PT.algEquivUnitsMapOfField_coe, Units.val_pow_eq_pow_val, zetaUnit_val]
  simpa [AlgEquiv.smul_def] using hm

theorem smul_zetaGen (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (g : K ≃ₐ[k] K) (m : ℕ) (hm : g • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m) :
    g • zetaGen (p := p) ζ hζ hζK = (m : ZMod p) • zetaGen (p := p) ζ hζ hζK := by
  have hmod : (zrou (p := p) ζ hζ hζK) ^ m
      = (zrou (p := p) ζ hζ hζK) ^ (m : ZMod p).val := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, zrou_coe]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ZMod.val_natCast, zetaUnit_val]
    have hp1 : (⟨ζ, hζK⟩ : K) ^ p = 1 :=
      Subtype.ext (by rw [IntermediateField.coe_pow]; exact hζ.pow_eq_one)
    conv_lhs => rw [← Nat.mod_add_div m p]
    rw [pow_add, pow_mul, hp1, one_pow, mul_one]
  apply Additive.toMul.injective
  rw [smul_zetaGen_toMul ζ hζ hζK g m hm, zmod_smul_zetaGen_toMul ζ hζ hζK (m : ZMod p)]
  exact hmod

theorem smul_zetaGen_eq_zero_iff (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (c : ZMod p) : c • zetaGen (p := p) ζ hζ hζK = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h1 : (zrou (p := p) ζ hζ hζK) ^ c.val = 1 := by
      rw [← zmod_smul_zetaGen_toMul ζ hζ hζK c]
      rw [h]
      rfl
    have h2 : (zetaUnit (p := p) ζ hζ hζK) ^ c.val = 1 := by
      have h3 := Subtype.ext_iff.mp h1
      rwa [SubmonoidClass.coe_pow, zrou_coe] at h3
    have h4 : (⟨ζ, hζK⟩ : K) ^ c.val = 1 := by
      have h5 : (((zetaUnit (p := p) ζ hζ hζK : Kˣ) : K)) ^ c.val = (1 : K) := by
        rw [← Units.val_pow_eq_pow_val, h2]; rfl
      rwa [zetaUnit_val] at h5
    have h6 : ζ ^ c.val = 1 := by
      have h7 : (((⟨ζ, hζK⟩ : K) ^ c.val : K) : Ω) = ((1 : K) : Ω) := congrArg Subtype.val h4
      rw [IntermediateField.coe_pow] at h7
      simpa using h7
    have h9 : p ∣ c.val := hζ.dvd_of_pow_eq_one c.val h6
    have h10 : c.val < p := ZMod.val_lt c
    have h11 : c.val = 0 := by
      by_contra hne
      have hpos : 0 < c.val := Nat.pos_of_ne_zero hne
      have hle : p ≤ c.val := Nat.le_of_dvd hpos h9
      omega
    rw [← ZMod.natCast_zmod_val c, h11, Nat.cast_zero]
  · intro h; rw [h, zero_smul]

theorem exists_smul_zetaGen (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (x : MuAdd p K) : ∃ c : ZMod p, x = c • zetaGen (p := p) ζ hζ hζK := by
  have hup : (((Additive.toMul x : rootsOfUnity p K) : Kˣ) : K) ^ p = 1 :=
    (mem_rootsOfUnity' p ((Additive.toMul x : rootsOfUnity p K) : Kˣ)).mp (Additive.toMul x).2
  have hupΩ : (((Additive.toMul x : rootsOfUnity p K) : Kˣ) : Ω) ^ p = 1 := by
    have h1 : (((((Additive.toMul x : rootsOfUnity p K) : Kˣ) : K)) ^ p : Ω)
        = ((1 : K) : Ω) := congrArg Subtype.val hup
    simpa using h1
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hupΩ
  refine ⟨i, ?_⟩
  have hcoee : ((Additive.toMul x : rootsOfUnity p K) : Kˣ) = (zetaUnit (p := p) ζ hζ hζK) ^ i := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, zetaUnit_val]
    exact Subtype.ext (by rw [IntermediateField.coe_pow]; exact hi.symm)
  have hu_eq : (Additive.toMul x : rootsOfUnity p K) = (zrou (p := p) ζ hζ hζK) ^ i := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, zrou_coe]
    exact hcoee
  rw [show x = Additive.ofMul (Additive.toMul x) from rfl, hu_eq,
    Nat.cast_smul_eq_nsmul (ZMod p) i (zetaGen (p := p) ζ hζ hζK)]
  exact (ofMul_nsmul i (zrou (p := p) ζ hζ hζK)).symm

end MuCyclic

/-! ## The coefficient isomorphism `DualMod p T ≃ₗ μ_p` -/

section CoeffIso

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : Ω} {T : Type} [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- The linear map `φ ↦ φ (Ach.t0) • ζ` from `DualMod p T` to `μ_p ⊆ K`. -/
noncomputable def dualModToMu (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Work.SSGRoute.DualMod p T →ₗ[ZMod p] MuAdd p K where
  toFun φ := φ (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK
  map_add' φ ψ := by
    rw [LinearMap.add_apply, add_smul]
  map_smul' c φ := by
    rw [RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul, mul_smul]

@[simp] theorem dualModToMu_apply
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (φ : Work.SSGRoute.DualMod p T) :
    dualModToMu hT hζ hζK φ = φ (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK := rfl

theorem dualModToMu_surjective
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Function.Surjective (dualModToMu (p := p) (K := K) hT hζ hζK) := by
  intro x
  obtain ⟨c, hc⟩ := exists_smul_zetaGen (p := p) ζ hζ hζK x
  refine ⟨c • Ach.coord p T hT.1, ?_⟩
  rw [dualModToMu_apply, LinearMap.smul_apply, Ach.coord_t0, smul_eq_mul, mul_one]
  exact hc.symm

theorem dualModToMu_injective
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Function.Injective (dualModToMu (p := p) (K := K) hT hζ hζK) := by
  intro φ ψ h
  rw [dualModToMu_apply, dualModToMu_apply] at h
  have h' : (φ (Ach.t0 p T hT.1) - ψ (Ach.t0 p T hT.1)) • zetaGen (p := p) ζ hζ hζK = 0 := by
    rw [sub_smul, h, sub_self]
  have h2 : φ (Ach.t0 p T hT.1) = ψ (Ach.t0 p T hT.1) :=
    sub_eq_zero.mp ((smul_zetaGen_eq_zero_iff ζ hζ hζK _).mp h')
  ext t
  rw [← Ach.smul_coord_t0 p T hT.1 t, map_smul, map_smul, h2]

/-- **The coefficient isomorphism** `DualMod p T ≃ₗ[ZMod p] μ_p ⊆ K` for a cyclotomic dual
`T`. -/
noncomputable def dualModEquivMu
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Work.SSGRoute.DualMod p T ≃ₗ[ZMod p] MuAdd p K :=
  LinearEquiv.ofBijective (dualModToMu (p := p) (K := K) hT hζ hζK)
    ⟨dualModToMu_injective hT hζ hζK, dualModToMu_surjective hT hζ hζK⟩

@[simp] theorem dualModEquivMu_apply
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (φ : Work.SSGRoute.DualMod p T) :
    dualModEquivMu hT hζ hζK φ = φ (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK :=
  rfl

/-- **The coefficient isomorphism is `Gal(K/k)`-equivariant.** -/
theorem dualModEquivMu_smul
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (g : K ≃ₐ[k] K)
    (φ : Work.SSGRoute.DualMod p T) :
    dualModEquivMu hT hζ hζK (g • φ) = g • dualModEquivMu hT hζ hζK φ := by
  obtain ⟨m, hm⟩ := exists_smul_zeta_eq_pow (p := p) ζ hζ hζK g
  have h1 : g • φ = (m : ZMod p) • φ := dualMod_smul_eq hζK hT g m hm φ
  have h2 : g • zetaGen (p := p) ζ hζ hζK = (m : ZMod p) • zetaGen (p := p) ζ hζ hζK :=
    smul_zetaGen ζ hζ hζK g m hm
  calc dualModEquivMu hT hζ hζK (g • φ)
      = (g • φ) (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK :=
        dualModEquivMu_apply hT hζ hζK (g • φ)
    _ = ((m : ZMod p) • φ) (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK := by rw [h1]
    _ = ((m : ZMod p) * φ (Ach.t0 p T hT.1)) • zetaGen (p := p) ζ hζ hζK := by
          rw [LinearMap.smul_apply, smul_eq_mul]
    _ = (φ (Ach.t0 p T hT.1) * (m : ZMod p)) • zetaGen (p := p) ζ hζ hζK := by rw [mul_comm]
    _ = φ (Ach.t0 p T hT.1) • ((m : ZMod p) • zetaGen (p := p) ζ hζ hζK) := by rw [mul_smul]
    _ = φ (Ach.t0 p T hT.1) • (g • zetaGen (p := p) ζ hζ hζK) := by rw [← h2]
    _ = g • (φ (Ach.t0 p T hT.1) • zetaGen (p := p) ζ hζ hζK) := by
          rw [← smul_comm g (φ (Ach.t0 p T hT.1)) (zetaGen (p := p) ζ hζ hζK)]
    _ = g • dualModEquivMu hT hζ hζK φ := by rw [dualModEquivMu_apply]

end CoeffIso

/-! ## The natural action of a subgroup of `G_k` on `Ωˣ` -/

section SubgroupAction

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- The natural action of a subgroup `H ≤ G_k` on `Additive Ωˣ` (restriction of the action of
`G_k`). -/
noncomputable instance instDistribMulActionSubgroupAddUnits (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    DistribMulAction ↥H (Additive (Units Ω)) where
  smul h a := (h : Ω ≃ₐ[k] Ω) • a
  one_smul a := by
    show ((1 : ↥H) : Ω ≃ₐ[k] Ω) • a = a
    rw [show ((1 : ↥H) : Ω ≃ₐ[k] Ω) = 1 from rfl, one_smul]
  mul_smul h₁ h₂ a := by
    show ((h₁ * h₂ : ↥H) : Ω ≃ₐ[k] Ω) • a = (h₁ : Ω ≃ₐ[k] Ω) • ((h₂ : Ω ≃ₐ[k] Ω) • a)
    rw [show ((h₁ * h₂ : ↥H) : Ω ≃ₐ[k] Ω)
        = (h₁ : Ω ≃ₐ[k] Ω) * (h₂ : Ω ≃ₐ[k] Ω) from rfl, mul_smul]
  smul_zero h := smul_zero _
  smul_add h a b := smul_add _ _ _

@[simp] theorem subgroupAddUnits_smul (H : Subgroup (Ω ≃ₐ[k] Ω)) (h : ↥H)
    (a : Additive (Units Ω)) :
    h • a = (h : Ω ≃ₐ[k] Ω) • a := rfl

end SubgroupAction

end

end MupCard
end Work.SSGRoute.PTembedding

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
import Submission.Work.SSGRoute.PTembedding.kbdDefs
import Submission.Work.SSGRoute.PTembedding.mul_natCard_indexP_subgroups
import Submission.Work.SSGRoute.PTembedding.natCard_galoisExtensions_maxAbelian
import Submission.Work.SSGRoute.PTembedding.natCard_isDegPLevel_eq_indexP_subgroups
import Submission.Work.SSGRoute.PTembedding.natCard_lcHoms_eq_degreeP
import Submission.Work.SSGRoute.finite_localField_homs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace Work.SSGRoute.PTembedding


section Helpers

/-- The `p`-th powers lie in every subgroup of index `p`. -/
lemma powMonoidHom_range_le_of_index (G : Type*) [CommGroup G] {p : ℕ} (M : Subgroup G)
    (hM : M.index = p) : (powMonoidHom p : G →* G).range ≤ M := by
  intro x hx
  rw [MonoidHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [← hM]
  exact Subgroup.pow_index_mem M y

/-- If the `p`-th power quotient of an abelian group is finite, then the group has only
finitely many subgroups of index `p`. -/
lemma finite_indexP_subgroups_of_finite_quot (G : Type*) [CommGroup G] (p : ℕ)
    [Finite (G ⧸ (powMonoidHom p : G →* G).range)] :
    Finite {M : Subgroup G // M.index = p} := by
  have key : ∀ M : {M : Subgroup G // M.index = p},
      M.1 = (M.1.map (QuotientGroup.mk' (powMonoidHom p : G →* G).range)).comap
        (QuotientGroup.mk' (powMonoidHom p : G →* G).range) := by
    intro M
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr (powMonoidHom_range_le_of_index G M.1 M.2)]
  refine Finite.of_injective
    (fun M : {M : Subgroup G // M.index = p} =>
      (M.1.map (QuotientGroup.mk' (powMonoidHom p : G →* G).range) : Subgroup _))
    ?_
  intro M₁ M₂ h
  have h' : Subgroup.map (QuotientGroup.mk' ((powMonoidHom p : G →* G).range)) M₁.1
      = Subgroup.map (QuotientGroup.mk' ((powMonoidHom p : G →* G).range)) M₂.1 := h
  have h₁ := key M₁
  have h₂ := key M₂
  rw [h'] at h₁
  exact Subtype.ext (h₁.trans h₂.symm)

end Helpers

section Finiteness

variable {K F' : Type*} [Field K] [Field F'] [Algebra K F']

/-- A group homomorphism with open kernel into a group is locally constant (for the discrete
topology on the target, when the target is viewed as a topological group). -/
lemma isLocallyConstant_of_isOpen_ker {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type*} [Group A] (χ : G →* A) (h : IsOpen (χ.ker : Set G)) :
    IsLocallyConstant χ := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  by_cases hy : ∃ x, χ x = y
  · obtain ⟨x, hx⟩ := hy
    have h1 : χ ⁻¹' {y} = x • (χ.ker : Set G) := by
      ext z
      rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_smul_set]
      constructor
      · intro hz
        refine ⟨x⁻¹ * z, ?_, ?_⟩
        · show χ (x⁻¹ * z) = 1
          rw [map_mul, map_inv, hz, hx, inv_mul_cancel]
        · show x * (x⁻¹ * z) = z
          group
      · rintro ⟨k, hk, hkz⟩
        rw [← hkz, smul_eq_mul, map_mul, MonoidHom.mem_ker.mp hk, mul_one, hx]
    rw [h1]
    exact h.leftCoset x
  · have hempty : χ ⁻¹' {y} = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩
      exact hy ⟨x, hx⟩
    rw [hempty]
    exact isOpen_empty

end Finiteness

section FiniteExtensions

variable {K F' : Type*} [Field K] [Field F'] [Algebra K F'] [IsSepClosure K F']

/-- **Every degree-`p` Galois subextension carries a nontrivial locally constant character whose
kernel is its fixing subgroup.** -/
lemma exists_lcHoms_ker_eq_fixingSubgroup (p : ℕ) [Fact p.Prime]
    {L : IntermediateField K F'} (hgal : IsGalois K L) (hdeg : Module.finrank K L = p) :
    ∃ χ : ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[K] F')), χ.1 ≠ 1 ∧
      χ.1.ker = L.fixingSubgroup := by
  haveI : FiniteDimensional K ↥L :=
    FiniteDimensional.of_finrank_pos (by rw [hdeg]; exact (Fact.out : p.Prime).pos)
  haveI : Normal K ↥L := hgal.to_normal
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L) :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥L) F'
  have hcard : Nat.card (↥L ≃ₐ[K] ↥L) = p := by
    rw [IsGalois.card_aut_eq_finrank K ↥L, hdeg]
  haveI hNz : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let φ : (↥L ≃ₐ[K] ↥L) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hcard (Work.SSGRoute.natCard_multiplicative_zmod p)
  have hker : (φ.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L)).ker
      = L.fixingSubgroup := by
    rw [MonoidHom.ker_comp_of_injective (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L)
      φ.toMonoidHom φ.injective]
    change (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L).ker = L.fixingSubgroup
    exact IntermediateField.restrictNormalHom_ker L
  have hlg : IsLocallyConstant
      (φ.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L)) := by
    refine isLocallyConstant_of_isOpen_ker _ ?_
    rw [hker]
    exact IntermediateField.fixingSubgroup_isOpen L
  refine ⟨⟨_, hlg⟩, ?_, hker⟩
  intro h1
  have hker_top : L.fixingSubgroup = ⊤ := by
    rw [← hker,
      show φ.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L) = 1 from h1,
      MonoidHom.ker_one]
  have h1' : Module.finrank K ↥L = 1 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (F := K) F' L, hker_top,
      Subgroup.index_top]
  have h2 : p ≤ 1 := by rw [← hdeg, h1']
  exact absurd h2 (by have := (Fact.out : p.Prime).two_le; omega)

/-- **Finitely many locally constant characters imply finitely many degree-`p` Galois
subextensions.** -/
theorem finite_degreeP_extensions_of_finite_lcHoms (p : ℕ) [Fact p.Prime]
    [Finite ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[K] F'))] :
    Finite {L : IntermediateField K F' // IsGalois K L ∧ Module.finrank K L = p} := by
  classical
  let cls : {L : IntermediateField K F' // IsGalois K L ∧ Module.finrank K L = p} →
      ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[K] F')) := fun L =>
    Classical.choose (exists_lcHoms_ker_eq_fixingSubgroup (K := K) (F' := F') p L.2.1 L.2.2)
  have hcls : ∀ L, (cls L).1.ker = L.1.fixingSubgroup := fun L =>
    (Classical.choose_spec
      (exists_lcHoms_ker_eq_fixingSubgroup (K := K) (F' := F') p L.2.1 L.2.2)).2
  refine Finite.of_injective cls ?_
  intro L₁ L₂ h
  have hk : (L₁.1).fixingSubgroup = (L₂.1).fixingSubgroup := by
    rw [← hcls L₁, ← hcls L₂, h]
  exact Subtype.ext (by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L₁.1,
      ← InfiniteGalois.fixedField_fixingSubgroup L₂.1, hk])

end FiniteExtensions


section Main

open scoped Classical Pointwise

/-- **The locally constant characters of the local absolute Galois group are the units mod `p`-th
powers.**  For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω` and a prime
`p`: the continuous characters `Gal(k̄_𝔭/k_𝔭) → 𝔽_p` of the local absolute Galois group at `A` are
as numerous as `k_𝔭ˣ ⧸ (k_𝔭ˣ)^p`.

This is local Kummer theory / local Tate duality in the form needed by the local base case: both
sides are counted by the index-`p` subgroups of `k_𝔭ˣ` — the characters through their open
kernels, the unit quotient through the classification of the abelian extensions of degree `p` of
the completion by their norm groups. -/
theorem lcHoms_localUnits
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Nat.card ↥(Work.SSGRoute.lcHoms p (Work.SSGRoute.PTembedding.localGalOf k A hA))
      = Nat.card ((Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ ⧸
          ((powMonoidHom p : (Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ →*
            (Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ).range)) := by
  classical
  -- the prime of `k` below the place `A`, and the completion `κ = k_𝔭`
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    Submission.NeukirchUchida.primeOf A hA
  have hκ : Work.SSGRoute.PTembedding.localFieldOf k A hA = Q.adicCompletion k := rfl
  have hκc : Work.SSGRoute.PTembedding.localClosureOf k A hA
      = SeparableClosure (Q.adicCompletion k) := rfl
  have hgal : Work.SSGRoute.PTembedding.localGalOf k A hA
      = (SeparableClosure (Q.adicCompletion k) ≃ₐ[Q.adicCompletion k]
          SeparableClosure (Q.adicCompletion k)) := rfl
  -- the local reciprocity datum at `A`
  let D : NK.LocalCFT.ArtinReciprocity (Q.adicCompletion k) (SeparableClosure (Q.adicCompletion k)) :=
    (NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion Q
      (NK.NUV2.kernelCondition_all k Q).some).some
  -- characteristic zero and the finiteness of the `p`-th power class group of `κ`
  haveI hcz : CharZero (Q.adicCompletion k) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion Q
  haveI hKum : Finite ((Q.adicCompletion k)ˣ ⧸
      (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range) :=
    Work.SSGRoute.finite_powClass_localField (Q.adicCompletion k) p (Fact.out : p.Prime)
  haveI hFinM : Finite {M : Subgroup (Q.adicCompletion k)ˣ // M.index = p} :=
    finite_indexP_subgroups_of_finite_quot _ p
  -- finiteness of the locally constant characters (from the workspace)
  haveI hFinHoms : Finite {χ : Gal(SeparableClosure (Q.adicCompletion k) / (Q.adicCompletion k)) →*
      Multiplicative (ZMod p) //
        IsOpen (χ.ker : Set (Gal(SeparableClosure (Q.adicCompletion k) / (Q.adicCompletion k))))} :=
    Work.SSGRoute.finite_localField_homs k Q p (ZMod p)
  haveI hFinLc : Finite ↥(Work.SSGRoute.lcHoms p (SeparableClosure (Q.adicCompletion k) ≃ₐ[
      Q.adicCompletion k] SeparableClosure (Q.adicCompletion k))) := by
    refine Finite.of_injective
      (fun χ : ↥(Work.SSGRoute.lcHoms p (SeparableClosure (Q.adicCompletion k) ≃ₐ[
          Q.adicCompletion k] SeparableClosure (Q.adicCompletion k))) =>
        (⟨χ.1, ?_⟩ : {χ : Gal(SeparableClosure (Q.adicCompletion k) / (Q.adicCompletion k)) →*
          Multiplicative (ZMod p) //
            IsOpen (χ.ker : Set (Gal(SeparableClosure (Q.adicCompletion k) /
              (Q.adicCompletion k))))})) ?_
    · show IsOpen ((χ.1).ker : Set (Gal(SeparableClosure (Q.adicCompletion k) /
        (Q.adicCompletion k))))
      exact χ.2.isOpen_fiber 1
    · intro a b h
      refine Subtype.ext ?_
      have hz := congrArg (fun z : {ψ : Gal(SeparableClosure (Q.adicCompletion k) /
          (Q.adicCompletion k)) →* Multiplicative (ZMod p) //
          IsOpen (ψ.ker : Set (Gal(SeparableClosure (Q.adicCompletion k) /
            (Q.adicCompletion k))))} =>
        (z : Gal(SeparableClosure (Q.adicCompletion k) / (Q.adicCompletion k)) →*
          Multiplicative (ZMod p))) h
      simpa using hz
  -- hence finiteness of the degree-`p` extensions
  haveI hFinB : Finite {L : IntermediateField (Q.adicCompletion k)
      (SeparableClosure (Q.adicCompletion k)) //
        IsGalois (Q.adicCompletion k) L ∧
          Module.finrank (Q.adicCompletion k) L = p} :=
    finite_degreeP_extensions_of_finite_lcHoms (K := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) p
  -- the character count and the count of the extensions
  have hA' : Nat.card ↥(Work.SSGRoute.lcHoms p
        (SeparableClosure (Q.adicCompletion k) ≃ₐ[Q.adicCompletion k]
          SeparableClosure (Q.adicCompletion k)))
      = 1 + (p - 1) * Nat.card {L : IntermediateField (Q.adicCompletion k)
          (SeparableClosure (Q.adicCompletion k)) //
            IsGalois (Q.adicCompletion k) L ∧
              Module.finrank (Q.adicCompletion k) L = p} :=
    natCard_lcHoms_eq_degreeP (K := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) p hFinB
  -- the reduction of the extensions inside `κ̄` to the levels of `κ^{ab}`
  have hB : Nat.card {L : IntermediateField (Q.adicCompletion k)
        (SeparableClosure (Q.adicCompletion k)) //
          IsGalois (Q.adicCompletion k) L ∧
            Module.finrank (Q.adicCompletion k) L = p}
      = Nat.card {L : IntermediateField (Q.adicCompletion k)
          ↥(NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion k)
            (SeparableClosure (Q.adicCompletion k))) //
          IsGalois (Q.adicCompletion k) ↥L ∧
            Module.finrank (Q.adicCompletion k) ↥L = p} :=
    natCard_galoisExtensions_maxAbelian (F := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) p
  -- the classification of the degree-`p` levels by the index-`p` subgroups of the units
  have hC : Nat.card {L : IntermediateField (Q.adicCompletion k)
        ↥(NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion k)
          (SeparableClosure (Q.adicCompletion k))) //
        IsGalois (Q.adicCompletion k) ↥L ∧
          Module.finrank (Q.adicCompletion k) ↥L = p}
      = Nat.card {M : Subgroup (Q.adicCompletion k)ˣ // M.index = p} := by
    exact natCard_isDegPLevel_eq_indexP_subgroups (F := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) D
  -- the count of the index-`p` subgroups by the `p`-th power quotient
  have hD : (p - 1) * Nat.card {M : Subgroup (Q.adicCompletion k)ˣ // M.index = p}
      = Nat.card ((Q.adicCompletion k)ˣ ⧸
          (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range) - 1 :=
    mul_natCard_indexP_subgroups p (Q.adicCompletion k)ˣ
  have hSpos : 1 ≤ Nat.card ((Q.adicCompletion k)ˣ ⧸
      (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
  change Nat.card ↥(Work.SSGRoute.lcHoms p (SeparableClosure (Q.adicCompletion k) ≃ₐ[
      Q.adicCompletion k] SeparableClosure (Q.adicCompletion k)))
    = Nat.card ((Q.adicCompletion k)ˣ ⧸
        (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range)
  calc Nat.card ↥(Work.SSGRoute.lcHoms p
        (SeparableClosure (Q.adicCompletion k) ≃ₐ[Q.adicCompletion k]
          SeparableClosure (Q.adicCompletion k)))
      = 1 + (p - 1) * Nat.card {L : IntermediateField (Q.adicCompletion k)
          (SeparableClosure (Q.adicCompletion k)) //
            IsGalois (Q.adicCompletion k) L ∧
              Module.finrank (Q.adicCompletion k) L = p} := hA'
    _ = 1 + (p - 1) * Nat.card {M : Subgroup (Q.adicCompletion k)ˣ // M.index = p} := by
        rw [hB, hC]
    _ = 1 + (Nat.card ((Q.adicCompletion k)ˣ ⧸
          (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range) - 1) := by
        rw [hD]
    _ = Nat.card ((Q.adicCompletion k)ˣ ⧸
          (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range) :=
        Nat.add_sub_cancel' hSpos

end Main

end Work.SSGRoute.PTembedding

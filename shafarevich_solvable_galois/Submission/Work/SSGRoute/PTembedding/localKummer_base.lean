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
import Submission.Work.GroupCohomology.H1_zmod_module
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
import Submission.Work.SSGRoute.PT.h1loc_finrank_trivialAction
import Submission.Work.SSGRoute.sha2_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local Kummer theory: the `M = 𝔽_p` base case of E7's perfectness

Second proof ingredient of **E7** (`Submission/Work/SSGRoute/PTembedding/localTatePairing_canonical`),
after the local Euler characteristic (`localEulerCharacteristic_of_residueChar`).

**Where Kummer theory enters.**  For the *trivial* coefficient module `M = Triv p = 𝔽_p` the Tate
dual is `M^∨(1) = DualMod p (𝔽_p ⊗ T) = Hom(T, 𝔽_p) ≅ μ_p` (the double dual of the line `T ≅ μ_p^∨`
under `IsCyclotomicDual`).  So the `M = 𝔽_p` case of the local duality `H¹(D_A,M) ≅ H¹(D_A,M^∨(1))^∨`
is the local Kummer isomorphism

  `H¹(k_v, μ_p) ≅ k_v^× ⧸ (k_v^×)^p`     (local Kummer / Hilbert 90),

and here it is stated in the dimension form E7's dimension count consumes:

  `dim H¹(D_A, 𝔽_p) = dim H¹(D_A, μ_p)`   at every place `A` over a finite prime.

**Why this is the right piece to isolate.**  E7's perfectness is proved by the dimension count
(local Euler characteristic + Tate duality in degrees 0/2); the *only* place where the arithmetic
of the coefficient module `𝔽_p` (as opposed to the formal dimension bookkeeping) enters is this
identification of `H¹(k_v, μ_p)` with the Kummer quotient.  Everything else is
`localEulerCharacteristic_of_residueChar` plus the degree-0/2 duality.

*Review note (2026-09-26):* the statement was reviewed **correct** (for every finite place, including
residue characteristic `p`), but the reviewer also pointed out that the workspace already contains
the equivalent equality `local_tate_duality_mup_dim` (`dim H¹(D_A, μ_p) = dim H¹(D_A, μ_p^∨(1))`, the
same equality with `μ_p` as *first* argument).  So this node is a *re-encoding* whenever that lemma
is reachable: it should then be obtained by transporting along the coefficient isomorphisms
(`Triv p ⊗ T ≅ T`, `DualMod p T ≅ μ_p`), not by redoing local CFT.  That lemma currently imports
`local_tate_duality_euler` and `local_tate_duality_02`, which are **absent from disk** — so the
*real* next node is the local duality input it needs (`Submission/Work/SSGRoute/PT/localDuality02.lean`
being the fresh version in the tree), and this file is the fallback statement of the Kummer content.

**Status.**  True; not yet in the workspace in this shape.  The arithmetic is available in the CFT
library in the completion vocabulary (`NK.NUV2.kernelCondition_all`, the local reciprocity law in
kernel form at every completion, and `NK.LocalKW`), and the comparison between the decomposition
group `D_A = decomp k A` and the completion `k_v` is the model bridge
`Work.SSGRoute.LTDDefs.H1locEquivH1cont` / `H2locEquivH2`.
-/

open scoped TensorProduct

namespace Work.SSGRoute.PTembedding

open Classical

noncomputable section

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]


/-! ## Push-forward of locally constant cocycles along an equivariant linear map

The coefficient module of the local cohomology `H1loc` of `LTDDefs/Basic.lean` is a finite
`𝔽_p[Gal(K/k)]`-module.  The lemmas below transport the whole cocycle model along a
`Gal(K/k)`-equivariant `𝔽_p`-linear map, and along an equivariant *isomorphism* they give the
invariance of the dimension `finrank (ZMod p) (H1loc ...)`.  This is the formal part of every
coefficient identification in the local lane (e.g. `Triv p ⊗ T ≅ T`, `DualMod p T ≅ μ_p`).
-/

section Transport

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {H : Subgroup (Ω ≃ₐ[k] Ω)}
  {M M' : Type} [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction (K ≃ₐ[k] K) M']
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M']

/-- The linear map of function modules induced by `e : M →ₗ M'`, `f ↦ e ∘ f`. -/
def pushLin (e : M →ₗ[ZMod p] M') : ((Ω ≃ₐ[k] Ω) → M) →ₗ[ZMod p] ((Ω ≃ₐ[k] Ω) → M') where
  toFun f := fun σ => e (f σ)
  map_add' f g := by ext σ; exact map_add e (f σ) (g σ)
  map_smul' c f := by ext σ; exact map_smul e c (f σ)

@[simp] lemma pushLin_apply (e : M →ₗ[ZMod p] M') (f : (Ω ≃ₐ[k] Ω) → M)
    (σ : Ω ≃ₐ[k] Ω) : pushLin e f σ = e (f σ) := rfl

/-- Push-forward preserves the `1`-cocycle condition. -/
lemma isCocycleOn_pushLin (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m)
    {f : (Ω ≃ₐ[k] Ω) → M} (hf : SSGRoute.IsCocycleOn (SSGRoute.res k K) H f) :
    SSGRoute.IsCocycleOn (SSGRoute.res k K) H (pushLin e f) := by
  intro x hx y hy
  show e (f (x * y)) = e (f x) + (SSGRoute.res k K x) • e (f y)
  rw [hf x hx y hy, map_add, he]

/-- Push-forward preserves local constancy. -/
lemma isLocConstOn_pushLin (e : M →ₗ[ZMod p] M') {f : (Ω ≃ₐ[k] Ω) → M}
    (hf : SSGRoute.IsLocConstOn H f) : SSGRoute.IsLocConstOn H (pushLin e f) := by
  obtain ⟨U, hUo, hU⟩ := hf
  refine ⟨U, hUo, fun g hg u hu huH => ?_⟩
  show e (f (g * u)) = e (f g)
  rw [hU g hg u hu huH]

/-- Push-forward sends coboundaries to coboundaries. -/
lemma isCoboundaryOn_pushLin (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m)
    {f : (Ω ≃ₐ[k] Ω) → M} (hf : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H f) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H (pushLin e f) := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨e m, fun g hg => ?_⟩
  show e (f g) = (SSGRoute.res k K g) • e m - e m
  rw [hm g hg, map_sub, he]

/-- Push-forward of locally constant cocycles along an equivariant linear map. -/
def pushCocycles (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    ↥(lcCocycles p k Ω K M H) →ₗ[ZMod p] ↥(lcCocycles p k Ω K M' H) where
  toFun f := ⟨pushLin e f.1, isCocycleOn_pushLin e he f.2.1, isLocConstOn_pushLin e f.2.2⟩
  map_add' f g := Subtype.ext (by ext σ; exact map_add e (f.1 σ) (g.1 σ))
  map_smul' c f := Subtype.ext (by ext σ; exact map_smul e c (f.1 σ))

@[simp] lemma pushCocycles_apply (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m)
    (f : ↥(lcCocycles p k Ω K M H)) (σ : Ω ≃ₐ[k] Ω) :
    (pushCocycles (K := K) (H := H) e he f).1 σ = e (f.1 σ) := rfl

/-- **Push-forward of the local `H¹`** along an equivariant linear map, induced on the quotient
`H1loc = lcCocycles ⧸ coboundaries`. -/
def H1locPush (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    H1loc p k Ω K M H →ₗ[ZMod p] H1loc p k Ω K M' H :=
  Submodule.mapQ (Submodule.comap (lcCocycles p k Ω K M H).subtype
      (coboundaries p k Ω K M H))
    (Submodule.comap (lcCocycles p k Ω K M' H).subtype (coboundaries p k Ω K M' H))
    (pushCocycles e he)
    (by
      intro x hx
      rw [Submodule.mem_comap] at hx ⊢
      exact isCoboundaryOn_pushLin e he hx)

/-- `H1locPush` on representatives: the class of `f` maps to the class of `e ∘ f`. -/
lemma H1locPush_mk (e : M →ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m)
    (f : ↥(lcCocycles p k Ω K M H)) :
    H1locPush (K := K) (H := H) e he (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (pushCocycles (K := K) (H := H) e he f) :=
  Submodule.mapQ_apply _ _ _ f

/-- **Equivariance passes to the inverse** of an equivariant linear equivalence. -/
lemma linearEquiv_symm_equivariant (e : M ≃ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    ∀ (g : K ≃ₐ[k] K) (m' : M'), e.symm (g • m') = g • e.symm m' := by
  intro g m'
  apply e.injective
  rw [he g (e.symm m'), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Push-forward along a `Gal(K/k)`-equivariant isomorphism of coefficient modules is a linear
isomorphism of the local `H¹`-groups. -/
def H1locEquiv (e : M ≃ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    H1loc p k Ω K M H ≃ₗ[ZMod p] H1loc p k Ω K M' H :=
  LinearEquiv.ofBijective (H1locPush e.toLinearMap he) (by
    have hs := linearEquiv_symm_equivariant (K := K) e he
    -- the class of a cocycle invariant
    have key : ∀ (y : H1loc p k Ω K M H),
        H1locPush (K := K) (H := H) e.symm.toLinearMap hs
          (H1locPush (K := K) (H := H) e.toLinearMap he y) = y := by
      intro y
      refine Submodule.Quotient.induction_on _ y (fun f => ?_)
      rw [H1locPush_mk, H1locPush_mk, Submodule.Quotient.eq]
      have h0 : pushCocycles (K := K) (H := H) e.symm.toLinearMap hs
          (pushCocycles (K := K) (H := H) e.toLinearMap he f) = f := by
        apply Subtype.ext
        ext σ
        simp
      rw [h0, sub_self]
      exact Submodule.zero_mem _
    have key' : ∀ (y : H1loc p k Ω K M' H),
        H1locPush (K := K) (H := H) e.toLinearMap he
          (H1locPush (K := K) (H := H) e.symm.toLinearMap hs y) = y := by
      intro y
      refine Submodule.Quotient.induction_on _ y (fun f => ?_)
      rw [H1locPush_mk, H1locPush_mk, Submodule.Quotient.eq]
      have h0 : pushCocycles (K := K) (H := H) e.toLinearMap he
          (pushCocycles (K := K) (H := H) e.symm.toLinearMap hs f) = f := by
        apply Subtype.ext
        ext σ
        simp
      rw [h0, sub_self]
      exact Submodule.zero_mem _
    refine ⟨fun a b hab => ?_, fun b => ⟨H1locPush (K := K) (H := H) e.symm.toLinearMap hs b,
      key' b⟩⟩
    have h := key (a - b)
    rw [map_sub, hab, sub_self, map_zero] at h
    exact sub_eq_zero.mp h.symm)

/-- **The local `H¹` is invariant under equivariant coefficient isomorphisms.** -/
theorem finrank_H1loc_eq_of_equiv (e : M ≃ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    Module.finrank (ZMod p) (H1loc p k Ω K M H)
      = Module.finrank (ZMod p) (H1loc p k Ω K M' H) :=
  LinearEquiv.finrank_eq (H1locEquiv e he)

/-- **The local `H⁰` is invariant under equivariant coefficient isomorphisms.** -/
theorem finrank_H0loc_eq_of_equiv (e : M ≃ₗ[ZMod p] M')
    (he : ∀ (g : K ≃ₐ[k] K) (m : M), e (g • m) = g • e m) :
    Module.finrank (ZMod p) ↥(H0loc p k Ω K M H)
      = Module.finrank (ZMod p) ↥(H0loc p k Ω K M' H) := by
  have hmem : ∀ m : M, m ∈ H0loc p k Ω K M H ↔ e m ∈ H0loc p k Ω K M' H := by
    intro m
    constructor
    · intro hm g hg
      rw [← he (SSGRoute.res k K g) m, hm g hg]
    · intro hm g hg
      have h1 : e ((SSGRoute.res k K g) • m) = e m := by rw [he, hm g hg]
      exact e.injective h1
  let F : ↥(H0loc p k Ω K M H) →ₗ[ZMod p] ↥(H0loc p k Ω K M' H) :=
    { toFun := fun m => ⟨e m, (hmem m).mp m.2⟩
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by ext; simp }
  have hF : Function.Bijective F := by
    constructor
    · intro a b hab
      have h1 : e a = e b := by simpa [F] using congrArg Subtype.val hab
      exact Subtype.ext (e.injective h1)
    · intro y
      refine ⟨⟨e.symm y, (hmem _).mpr ?_⟩, ?_⟩
      · simpa using y.2
      · ext; simp [F]
  exact (LinearEquiv.ofBijective F hF).finrank_eq

end Transport

/-! ## The two coefficient identifications of the base case

The coefficient module `Triv p ⊗ T` of the target is `T` (the trivial module is the unit of the
tensor product), and dualising is contravariant, so

  `DualMod p (Triv p ⊗ T) ≃ₗ DualMod p T`   (`Gal(K/k)`-equivariantly).

Composing with `finrank_H1loc_eq_of_equiv` reduces the target to the *pure Kummer* statement that
`H¹(D_A, 𝔽_p)` and `H¹(D_A, μ_p)` have the same dimension, where `μ_p = DualMod p T` — the base
case of local Tate duality (local Kummer: `H¹(k_v, μ_p) ≅ k_v^× ⧸ (k_v^×)^p` together with
`H¹(k_v, 𝔽_p) = Hom_cont(k_v^×, 𝔽_p) ≅ (k_v^× ⧸ (k_v^×)^p)^∨` from local class field theory).
-/

section CoeffIso

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {T : Type} [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- `𝔽_p ⊗ T ≅ T`, the trivial module being the unit of the tensor product (here `Triv p = 𝔽_p`). -/
def trivTensorEquiv : Work.SSGRoute.Triv p ⊗[ZMod p] T ≃ₗ[ZMod p] T :=
  TensorProduct.lid (ZMod p) T

@[simp] lemma trivTensorEquiv_tmul (a : Work.SSGRoute.Triv p) (t : T) :
    trivTensorEquiv (a ⊗ₜ[ZMod p] t) = a • t := TensorProduct.lid_tmul t a

/-- The action on the trivial module is trivial (definitionally). -/
@[simp] lemma triv_smul_eq (g : K ≃ₐ[k] K) (a : Work.SSGRoute.Triv p) : g • a = a := rfl

lemma trivTensorEquiv_smul (g : K ≃ₐ[k] K) (x : Work.SSGRoute.Triv p ⊗[ZMod p] T) :
    trivTensorEquiv (g • x) = g • trivTensorEquiv x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul a t =>
    show trivTensorEquiv (g • (a ⊗ₜ[ZMod p] t)) = g • trivTensorEquiv (a ⊗ₜ[ZMod p] t)
    rw [show g • (a ⊗ₜ[ZMod p] t) = (g • a) ⊗ₜ[ZMod p] (g • t) from by simp,
      trivTensorEquiv_tmul, trivTensorEquiv_tmul]
    rw [triv_smul_eq, smul_comm g a t]

/-- The contragredient of a linear equivalence. -/
def dualEquiv {X Y : Type} [AddCommGroup X] [Module (ZMod p) X]
    [AddCommGroup Y] [Module (ZMod p) Y] (e : X ≃ₗ[ZMod p] Y) :
    Work.SSGRoute.DualMod p Y ≃ₗ[ZMod p] Work.SSGRoute.DualMod p X where
  toFun φ := φ.comp e.toLinearMap
  invFun ψ := ψ.comp e.symm.toLinearMap
  left_inv φ := by ext y; simp
  right_inv ψ := by ext x; simp
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

@[simp] lemma dualEquiv_apply {X Y : Type} [AddCommGroup X] [Module (ZMod p) X]
    [AddCommGroup Y] [Module (ZMod p) Y] (e : X ≃ₗ[ZMod p] Y)
    (φ : Work.SSGRoute.DualMod p Y) (x : X) : dualEquiv e φ x = φ (e x) := rfl

lemma dualEquiv_smul {X Y : Type} [AddCommGroup X] [Module (ZMod p) X]
    [AddCommGroup Y] [Module (ZMod p) Y]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) Y] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) Y]
    (e : X ≃ₗ[ZMod p] Y) (he : ∀ (g : K ≃ₐ[k] K) (x : X), e (g • x) = g • e x)
    (g : K ≃ₐ[k] K) (ψ : Work.SSGRoute.DualMod p Y) :
    dualEquiv e (g • ψ) = g • dualEquiv e ψ := by
  ext x
  rw [dualEquiv_apply, Work.SSGRoute.DualMod.dualSMul_apply,
    Work.SSGRoute.DualMod.dualSMul_apply, dualEquiv_apply, he g⁻¹ x]

end CoeffIso

/-! ## The `𝔽_p`-module structure on the continuous cocycles of `AbsoluteKummer`

`Work.AbsoluteKummer.Z1 Γ M = Work.GroupCohomology.Z1 Γ M ⊓ C1c Γ M` is an `AddSubgroup` and
`Work.AbsoluteKummer.H1 Γ M` is its quotient by the coboundaries; neither came with a
`ZMod p`-module structure, although the generic group-cohomology layer has it
(`Work.GroupCohomology.H1zmod`, with `Z1m`/`B1m` as `ZMod p`-submodules of the cochains).  Without
that structure there is no `Module.finrank` for `H¹_c`, and hence no *linear* model bridge
`H1loc ≃ₗ H¹_c`.  Here is the missing `AbsoluteKummer` layer, built the same way as `H1zmod`:
locally constant cochains are closed under `𝔽_p`-scalars (`IsLocallyConstant.map`), hence so are
the continuous `1`-cocycles. -/

section ZmodCocycles

variable {p : ℕ} {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction Γ M] [SMulCommClass Γ (ZMod p) M]

/-- The locally constant `1`-cochains are closed under `𝔽_p`-scalars. -/
theorem zmod_smul_mem_C1c (a : ZMod p) {f : Γ → M}
    (hf : f ∈ Work.AbsoluteKummer.C1c Γ M) : a • f ∈ Work.AbsoluteKummer.C1c Γ M :=
  show Work.AbsoluteKummer.IsLocallyConstant (fun x => a • f x) from
    Work.AbsoluteKummer.IsLocallyConstant.map (fun y : M => a • y) hf

/-- The continuous `1`-cocycles `Z¹_c(Γ,M)` are closed under `𝔽_p`-scalars. -/
theorem zmod_smul_mem_Z1c (a : ZMod p) {f : Γ → M}
    (hf : f ∈ Work.AbsoluteKummer.Z1 Γ M) : a • f ∈ Work.AbsoluteKummer.Z1 Γ M := by
  simp only [Work.AbsoluteKummer.Z1, AddSubgroup.mem_inf] at hf ⊢
  exact ⟨Work.GroupCohomology.H1zmod.zmod_smul_mem_Z1 p Γ M a hf.1,
    zmod_smul_mem_C1c (p := p) a hf.2⟩

/-- `Z¹_c(Γ,M)` as a `ZMod p`-submodule of the cochain group `C¹(Γ,M) = (Γ → M)`. -/
noncomputable def Z1cMod : Submodule (ZMod p) (Γ → M) :=
  Submodule.mk (Work.AbsoluteKummer.Z1 Γ M).toAddSubmonoid
    (fun a _ hx => zmod_smul_mem_Z1c (p := p) (Γ := Γ) (M := M) a hx)

/-- The `𝔽_p`-module structure on `↥(Work.AbsoluteKummer.Z1 Γ M)`, transported across the
definitional equality of the subtypes `↥Z1cMod` and `↥(Work.AbsoluteKummer.Z1 Γ M)` (both are
`{f // f ∈ Z1}`, the same carrier expression). -/
noncomputable instance instModuleZ1c : Module (ZMod p) ↥(Work.AbsoluteKummer.Z1 Γ M) where
  smul c x := ⟨c • (x : Γ → M), by
    exact zmod_smul_mem_Z1c (p := p) (Γ := Γ) (M := M) c x.2⟩
  one_smul x := Subtype.ext (by
    funext g
    exact one_smul (ZMod p) ((x : Γ → M) g))
  mul_smul c d x := Subtype.ext (by
    funext g
    exact mul_smul c d ((x : Γ → M) g))
  smul_zero c := Subtype.ext (by
    funext g
    exact smul_zero (c : ZMod p))
  smul_add c x y := Subtype.ext (by
    funext g
    exact smul_add (c : ZMod p) ((x : Γ → M) g) ((y : Γ → M) g))
  add_smul c d x := Subtype.ext (by
    funext g
    exact add_smul c d ((x : Γ → M) g))
  zero_smul x := Subtype.ext (by
    funext g
    exact zero_smul (ZMod p) ((x : Γ → M) g))

/-- The scalar action of `instModuleZ1c` is pointwise, so the subtype coercion commutes with the
scalar multiplication (`rfl`, but `simp` needs it as a rewrite since the instance is a literal and
is not unfolded by `simp only`). -/
@[simp] lemma instModuleZ1c_coe_smul (c : ZMod p) (x : ↥(Work.AbsoluteKummer.Z1 Γ M)) :
    ((c • x : ↥(Work.AbsoluteKummer.Z1 Γ M)) : Γ → M) = c • (x : Γ → M) := rfl

/-- The `1`-coboundaries of the `AbsoluteKummer` model `B¹_c(Γ,M)` are closed under
`𝔽_p`-scalars: they are the range of `d⁰`, which is the generic statement
`Work.GroupCohomology.H1zmod.zmod_smul_mem_B1` (`Work.AbsoluteKummer.B1` *is*
`Work.GroupCohomology.B1`). -/
theorem zmod_smul_mem_B1c (a : ZMod p) {f : Γ → M}
    (hf : f ∈ Work.AbsoluteKummer.B1 Γ M) : a • f ∈ Work.AbsoluteKummer.B1 Γ M :=
  Work.GroupCohomology.H1zmod.zmod_smul_mem_B1 p Γ M a hf

/-- `B¹_c(Γ,M)` as a `ZMod p`-submodule of the cochain group `C¹(Γ,M) = (Γ → M)`. -/
noncomputable def B1cMod : Submodule (ZMod p) (Γ → M) :=
  Submodule.mk (Work.AbsoluteKummer.B1 Γ M).toAddSubmonoid
    (fun a _ hx => zmod_smul_mem_B1c (p := p) (Γ := Γ) (M := M) a hx)

@[simp] theorem mem_B1cMod (f : Γ → M) :
    f ∈ B1cMod (p := p) (Γ := Γ) (M := M) ↔ f ∈ Work.AbsoluteKummer.B1 Γ M := Iff.rfl

/-- **`B1Q`, the coboundaries inside the continuous `1`-cocycles.**  As a `ZMod p`-submodule of
`↥(Work.AbsoluteKummer.Z1 Γ M)` it is the comap of `B¹_c` along the subtype, i.e. its carrier is
`{x | x.1 ∈ B¹_c(Γ,M)}`; with it, the quotient `H¹_c = Z¹_c ⧸ B1Q` carries the `𝔽_p`-module
structure transported from `Z1cMod ⧸ B1cMod` (the next step of the linear model bridge).  The
declaration type is `Submodule (ZMod p) ↥Z¹_c`, definitionally the same structure as
`Submodule (ZMod p) ↥Z1cMod` because the two subtypes have the same carrier expression. -/
noncomputable def B1Q : Submodule (ZMod p) ↥(Work.AbsoluteKummer.Z1 Γ M) :=
  Submodule.comap (Z1cMod (p := p) (Γ := Γ) (M := M)).subtype
    (B1cMod (p := p) (Γ := Γ) (M := M))

/-- Membership in `B1Q`: a continuous `1`-cocycle lies in the coboundaries iff its underlying
function does. -/
theorem mem_B1Q (x : ↥(Work.AbsoluteKummer.Z1 Γ M)) :
    x ∈ B1Q (p := p) (Γ := Γ) (M := M) ↔ (x : Γ → M) ∈ Work.AbsoluteKummer.B1 Γ M :=
  Submodule.mem_comap

/-- **The `𝔽_p`-module structure on the continuous cohomology `H¹_c(Γ,M)`.**  The quotient
`↥Z¹_c ⧸ B1Q` carries the `𝔽_p`-module structure of a quotient of the `ZMod p`-module `↥Z1cMod`,
and `Work.AbsoluteKummer.H1 Γ M` (the quotient of the same subtype by the same carrier, written
with the `AddSubgroup` quotient notation) is definitionally that quotient, so the structure can be
carried over. -/
noncomputable instance instModuleH1c : Module (ZMod p) (Work.AbsoluteKummer.H1 Γ M) :=
  (inferInstance : Module (ZMod p) (↥(Work.AbsoluteKummer.Z1 Γ M) ⧸
    B1Q (p := p) (Γ := Γ) (M := M)))

end ZmodCocycles

/-! ## (i) The `→ₗ` versions of the restriction and extension maps

`restrictCocycle`/`extendCocycle` (`LTDDefs/H1loc_iso_H1cont.lean`, imported below) are additive
maps between the locally constant cocycle model and the continuous-cochain model of
`AbsoluteKummer`.  With the `ZMod p`-module structures of the previous section both sides are
`𝔽_p`-modules and the two maps are `𝔽_p`-linear (they act pointwise on the values).  These are the
maps from which the linear model bridge is built by `Submodule.mapQ`, with bijectivity from the two
`_sub_mem` lemmas.

*Note on the heartbeats:* the transported instances of the previous section give
`↥(Work.AbsoluteKummer.Z1 ↥H M)` a second route to its additive/`FunLike` structure, so instance
search on the coercions here is slow; the two definitions are wrapped in a local heartbeat raise,
and their bodies are written with explicit lambdas.

**Status.**  `restrictCocycleLin` is proved below.  `extendCocycleLin` is *not yet*: its
`map_smul'` reduces to the coercion equation `(c • x).1 = c • x.1` for `x : ↥(Z¹_c)` under the
*transported* instance `instModuleZ1c`, which is not `rfl` and which the available simp lemmas
(`Submodule.coe_smul`, `AddSubgroup.coe_smul`, `SetLike.coe_smul`) have not yet been matched
against.  The robust fix is to define `instModuleZ1c` (and `instModuleH1c`) by an explicit
structure literal with the *pointwise* scalar action `smul c x := ⟨c • x.1, …⟩` instead of
transporting the `Submodule` instance across the definitional equality of the subtypes: then the
coercion equation is `rfl` by construction, and the instance-search diamond that the transported
instance creates (two routes to the additive/`FunLike` structure of `↥Z¹_c`) disappears as well.
Note the local `set_option synthInstance.maxHeartbeats 800000 in` / `maxHeartbeats 1600000 in`
around the definition: without it instance search *times out* on the coercions. -/

section LinearBridge

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [IsAlgClosure k Ω]
  {H : Subgroup (Ω ≃ₐ[k] Ω)} {M : Type} [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  [DistribMulAction ↥H M]

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
/-- The restriction of a locally constant `1`-cocycle on `H` to `H`, as an `𝔽_p`-linear map. -/
noncomputable def restrictCocycleLin
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    (lcCocycles p k Ω K M H) →ₗ[ZMod p] ↥(Work.AbsoluteKummer.Z1 ↥H M) where
  toFun := fun f => restrictCocycle p k Ω K M H hcompat f
  map_add' := fun a b => map_add (restrictCocycle p k Ω K M H hcompat) a b
  map_smul' c f := by
    apply Subtype.ext
    funext h
    rfl

/-- The defining formula of `extendCocycle` (an `rfl`-lemma, so that `simp` can see through the
`→+` literal and reach the `if … then … else 0`). -/
@[simp] lemma extendCocycle_apply
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (x : ↥(Work.AbsoluteKummer.Z1 ↥H M)) (g : Ω ≃ₐ[k] Ω) :
    (extendCocycle p k Ω K M H hcompat x : (Ω ≃ₐ[k] Ω) → M) g
      = if hg : g ∈ H then (x : ↥H → M) ⟨g, hg⟩ else 0 := rfl


set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
/-- The extension by `0` of a locally constant crossed homomorphism on `H`, as an `𝔽_p`-linear
map. -/
noncomputable def extendCocycleLin
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    ↥(Work.AbsoluteKummer.Z1 ↥H M) →ₗ[ZMod p] (lcCocycles p k Ω K M H) where
  toFun := fun x => extendCocycle p k Ω K M H hcompat x
  map_add' := fun a b => map_add (extendCocycle p k Ω K M H hcompat) a b
  map_smul' c x := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ H
    · have hcoe : ∀ (c : ZMod p) (x : ↥(Work.AbsoluteKummer.Z1 ↥H M)),
          ((c • x : ↥(Work.AbsoluteKummer.Z1 ↥H M)) : ↥H → M) = c • (x : ↥H → M) :=
        fun c x => rfl
      simp only [extendCocycle_apply, dif_pos hg, hcoe, Submodule.coe_smul, Pi.smul_apply,
        RingHom.id_apply]
    · simp only [extendCocycle_apply, dif_neg hg, Submodule.coe_smul, Pi.smul_apply, smul_zero]

end LinearBridge


/-! ## The linear model bridge (forward map)

`H1loc = Z¹_loc ⧸ B¹` and `H¹_c = Z¹_c ⧸ B¹_c` are quotients of the two cocycle models, and
`restrictCocycleLin` is an `𝔽_p`-linear map between them; `Submodule.mapQ` therefore induces an
`𝔽_p`-linear map on the quotients, well defined by `restrictCocycle_mem_coboundaries`.  The
membership lemmas `extendCocycle_mem_coboundaries`, `extendCocycle_restrictCocycle_sub_mem` and
`restrictCocycle_extendCocycle_sub_mem` (all already proved) then turn this into the linear
equivalence, and `finrank_H1loc_eq_H1` lets the local lane compute `finrank H1loc` in the
continuous-cochain model `Work.AbsoluteKummer`.

*Binder note:* unlike the additive bridge `H1locEquivH1` of `LTDDefs/H1loc_iso_H1cont.lean`, the
linear one needs the `𝔽_p`-module structures on both cocycle models, so the section carries
`[SMulCommClass ↥H (ZMod p) M]`, `[TopologicalSpace ↥H]` and `[IsTopologicalGroup ↥H]` — the
instances required by `instModuleZ1c` and `instModuleH1c`. -/

section BridgeLinear

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [IsAlgClosure k Ω]
  {H : Subgroup (Ω ≃ₐ[k] Ω)} {M : Type} [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  [DistribMulAction ↥H M] [SMulCommClass ↥H (ZMod p) M] [IsTopologicalGroup ↥H]

/-- The forward `𝔽_p`-linear map of the model bridge: restriction to `H`, on the quotients. -/
noncomputable def H1locLinearFwd
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    H1loc p k Ω K M H →ₗ[ZMod p]
      (↥(Work.AbsoluteKummer.Z1 ↥H M) ⧸ (B1Q (p := p) (Γ := ↥H) (M := M))) :=
  Submodule.mapQ (cobQ p k Ω K M H) (B1Q (p := p) (Γ := ↥H) (M := M))
    (restrictCocycleLin (p := p) (k := k) (Ω := Ω) (K := K) (H := H) (M := M) hcompat)
    (by
      intro x hx
      rw [Submodule.mem_comap] at hx
      rw [Submodule.mem_comap, mem_B1Q]
      exact restrictCocycle_mem_coboundaries p k Ω K M H hcompat hx x.2)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
/-- The backward `𝔽_p`-linear map of the model bridge: extension by `0` off `H`, on the
quotients.  The source is the quotient `↥Z¹_c ⧸ B1Q` **written syntactically** (the same
type-former that `Submodule.mapQ` produces), so that no definitional equality between quotient
type-formers has to be checked here; the nominal identification with
`Work.AbsoluteKummer.H1 ↥H M` is supplied later by an explicit linear equivalence, the linear
analogue of `Work.GroupCohomology.H1zmod.e`. -/
noncomputable def H1locLinearBwd
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    (↥(Work.AbsoluteKummer.Z1 ↥H M) ⧸ (B1Q (p := p) (Γ := ↥H) (M := M))) →ₗ[ZMod p]
      H1loc p k Ω K M H :=
  Submodule.mapQ (B1Q (p := p) (Γ := ↥H) (M := M)) (cobQ p k Ω K M H)
    (extendCocycleLin (p := p) (k := k) (Ω := Ω) (K := K) (H := H) (M := M) hcompat)
    (by
      intro x hx
      rw [mem_B1Q] at hx
      rw [Submodule.mem_comap]
      exact extendCocycle_mem_coboundaries p k Ω K M H hcompat hx)

@[simp] lemma H1locLinearBwd_mk
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (x : ↥(Work.AbsoluteKummer.Z1 ↥H M)) :
    H1locLinearBwd (p := p) (k := k) (Ω := Ω) (K := K) (H := H) (M := M) hcompat
        (Submodule.Quotient.mk (p := B1Q (p := p) (Γ := ↥H) (M := M)) x)
      = Submodule.Quotient.mk (extendCocycleLin (p := p) (k := k) (Ω := Ω) (K := K)
          (H := H) (M := M) hcompat x) :=
  Submodule.mapQ_apply _ _ _ x

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
@[simp] lemma H1locLinearFwd_mk
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (f : ↥(lcCocycles p k Ω K M H)) :
    H1locLinearFwd (p := p) (k := k) (Ω := Ω) (K := K) (H := H) (M := M) hcompat
        (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (restrictCocycleLin (p := p) (k := k) (Ω := Ω) (K := K)
          (H := H) (M := M) hcompat f) :=
  Submodule.mapQ_apply _ _ _ f

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
/-- **The model bridge, in syntactic form**: `H1loc` is `𝔽_p`-linearly isomorphic to the quotient
`↥Z¹_c ⧸ B1Q` of the continuous `1`-cocycles by the coboundaries.  (The nominal identification of
that quotient with `Work.AbsoluteKummer.H1 ↥H M` is a separate, explicit linear equivalence, in the
style of `Work.GroupCohomology.H1zmod.e`.) -/
noncomputable def H1locLinearEquivQuot
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    H1loc p k Ω K M H ≃ₗ[ZMod p]
      (↥(Work.AbsoluteKummer.Z1 ↥H M) ⧸ (B1Q (p := p) (Γ := ↥H) (M := M))) := by
  have hleft : ∀ y : H1loc p k Ω K M H,
      H1locLinearBwd (p := p) (k := k) (Ω := Ω) (K := K) (H := H) (M := M) hcompat
        (H1locLinearFwd (p := p) (k := k) (Ω := Ω) (K := K) (H := H) (M := M) hcompat y)
        = y := by
    intro y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (p := cobQ p k Ω K M H) y
    rw [H1locLinearFwd_mk, H1locLinearBwd_mk, Submodule.Quotient.eq]
    exact extendCocycle_restrictCocycle_sub_mem p k Ω K M H hcompat f
  have hright : ∀ z : ↥(Work.AbsoluteKummer.Z1 ↥H M) ⧸ (B1Q (p := p) (Γ := ↥H) (M := M)),
      H1locLinearFwd (p := p) (k := k) (Ω := Ω) (K := K) (H := H) (M := M) hcompat
        (H1locLinearBwd (p := p) (k := k) (Ω := Ω) (K := K) (H := H) (M := M) hcompat z)
        = z := by
    intro z
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective
      (p := B1Q (p := p) (Γ := ↥H) (M := M)) z
    rw [H1locLinearBwd_mk, H1locLinearFwd_mk, Submodule.Quotient.eq, mem_B1Q]
    exact restrictCocycle_extendCocycle_sub_mem p k Ω K M H hcompat c
  exact LinearEquiv.ofBijective
    (H1locLinearFwd (p := p) (k := k) (Ω := Ω) (K := K) (H := H) (M := M) hcompat)
    ⟨fun a b hab => by rw [← hleft a, hab, hleft b], fun z => ⟨_, hright z⟩⟩

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
/-- **The dimension of the local `H¹`, in syntactic form.** -/
theorem finrank_H1loc_eq_finrank_quot
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    Module.finrank (ZMod p) (H1loc p k Ω K M H)
      = Module.finrank (ZMod p)
          (↥(Work.AbsoluteKummer.Z1 ↥H M) ⧸ (B1Q (p := p) (Γ := ↥H) (M := M))) :=
  LinearEquiv.finrank_eq
    (H1locLinearEquivQuot (p := p) (k := k) (Ω := Ω) (K := K) (H := H) (M := M) hcompat)

end BridgeLinear



/-! ## Node (1), last step: the pointwise content of `Z¹_c(↥H, 𝔽_p) = (Γ^{ab} ⧸ p)^∨`

A homomorphism `φ` from a group `Γ` into the additive group `𝔽_p = ZMod p` is invariant under
commutation (the target is commutative) and kills `p`-th powers (`p • φ g = 0`).  Together these
say precisely that `φ` factors through the abelianization modulo `p`-th powers — the step that
identifies the locally constant homomorphisms `↥H → 𝔽_p` with the `𝔽_p`-dual of the `p`-Frattini
quotient `Γ^{ab} ⧸ (Γ^{ab})^p`; the dimension transfer is then free by
`Subspace.dual_finrank_eq`. -/

section Pointwise

variable {Γ : Type} [Group Γ] {p : ℕ}

/-- An additive homomorphism from a group into `𝔽_p` is invariant under commutation. -/
theorem zmod_addHom_mul_comm (φ : Γ → ZMod p) (hφ : ∀ g h : Γ, φ (g * h) = φ g + φ h)
    (g h : Γ) : φ (g * h) = φ (h * g) := by
  rw [hφ g h, hφ h g, add_comm]

/-- An additive homomorphism from a group into `𝔽_p` kills `p`-th powers. -/
theorem zmod_addHom_pow_eq_zero (φ : Γ → ZMod p)
    (hφ : ∀ g h : Γ, φ (g * h) = φ g + φ h) (g : Γ) : φ (g ^ p) = 0 := by
  have h1 : φ 1 = 0 := by
    have h := hφ 1 1
    rw [mul_one] at h
    exact add_left_cancel (by rw [h.symm, add_zero])
  have hpow : ∀ n : ℕ, φ (g ^ n) = n • φ g := by
    intro n
    induction n with
    | zero => rw [pow_zero, h1, zero_nsmul]
    | succ n ih => rw [pow_succ, hφ, ih, succ_nsmul, add_comm]
  rw [hpow p, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- **An additive hom from a group into `𝔽_p` kills commutators** — the precise sense in which it
factors through the abelianization `Γ^{ab}` (the converse half, building a hom out of a functional
on `Γ^{ab} ⧸ p̄`, is the surjectivity side of node (1)). -/
theorem zmod_addHom_commutator_eq_zero (φ : Γ → ZMod p)
    (hφ : ∀ g h : Γ, φ (g * h) = φ g + φ h) (g h : Γ) :
    φ (g * h * g⁻¹ * h⁻¹) = 0 := by
  have h1 : φ 1 = 0 := by
    have h := hφ 1 1
    rw [mul_one] at h
    exact add_left_cancel (by rw [h.symm, add_zero])
  have hinv : ∀ g : Γ, φ g⁻¹ = -φ g := by
    intro g
    have h := hφ g g⁻¹
    rw [mul_inv_cancel, h1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  calc φ (g * h * g⁻¹ * h⁻¹)
      = φ ((g * h) * (g⁻¹ * h⁻¹)) := by rw [mul_assoc, mul_assoc]
    _ = φ (g * h) + φ (g⁻¹ * h⁻¹) := hφ _ _
    _ = (φ g + φ h) + (φ g⁻¹ + φ h⁻¹) := by rw [hφ g h, hφ g⁻¹ h⁻¹]
    _ = 0 := by rw [hinv g, hinv h]; abel

end Pointwise


/-! ## Bridge lemmas for `Additive`/`Multiplicative` and `ZMod`-scalars (published)

These identifications were needed four times over while building `abHom`/`quotHom`/`homOfQuot`,
each time as a bare `show … from rfl` because Mathlib has no named lemma for them
(`Additive.ofMul_mul`, `Additive.ofMul_one`, `Multiplicative.ofAdd_add`, `Multiplicative.ofAdd_zero`,
`Additive.toMul_add`, `ZMod.smul_eq_nsmul` were all confirmed absent).  They are `rfl`-level, and
publishing them as `[simp]` lemmas in this lane's vocabulary retires the exposition tax. -/

section AdditiveMultiplicativeBridge

/-- `Additive.ofMul` turns a product into a sum (`rfl`-level). -/
@[simp] theorem ofMul_mul {α : Type*} [Mul α] (a b : α) :
    Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b := rfl

/-- `Additive.ofMul` turns `1` into `0` (`rfl`-level). -/
@[simp] theorem ofMul_one {α : Type*} [One α] :
    Additive.ofMul (1 : α) = 0 := rfl

/-- `Additive.toMul` turns a sum into a product (`rfl`-level). -/
@[simp] theorem toMul_add {α : Type*} [Mul α] (a b : Additive α) :
    Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b := rfl

/-- `Multiplicative.ofAdd` turns a sum into a product (`rfl`-level). -/
@[simp] theorem ofAdd_add {α : Type*} [Add α] (a b : α) :
    Multiplicative.ofAdd (a + b) = Multiplicative.ofAdd a * Multiplicative.ofAdd b := rfl

/-- `Multiplicative.ofAdd` turns `0` into `1` (`rfl`-level). -/
@[simp] theorem ofAdd_zero {α : Type*} [Zero α] :
    Multiplicative.ofAdd (0 : α) = 1 := rfl

/-- In any `ZMod p`-module, the scalar action is the action of the representative:
`r • m = r.val • m`.  (Mathlib has no named lemma for this — `ZMod.smul_eq_nsmul` is absent — but
the workspace does, at `Work.CohomologicalShrinking.naturalAlpha.psiLin_zmod_smul_eq_nsmul`, where it
is stated for an *arbitrary* `ZMod p`-module; this is the export in the local lane's vocabulary.) -/
@[simp] theorem zmod_smul_eq_nsmul_val {p : ℕ} [NeZero p] {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] (r : ZMod p) (m : M) : r • m = r.val • m :=
  Work.CohomologicalShrinking.naturalAlpha.psiLin_zmod_smul_eq_nsmul p r m

end AdditiveMultiplicativeBridge

/-! ## Node (1): the carrier `Γ^{ab} ⧸ p̄`

The `p`-Frattini quotient of the abelianization, written additively: the closure `p̄` of the
`p`-multiples in `Additive (Abelianization Γ)`, and the quotient `Γ^{ab} ⧸ p̄`, which is an
`AddCommGroup` of exponent `p`.  (That quotient, not the abelianization itself, is what carries the
`𝔽_p`-module structure: `Γ^{ab}` may have elements of order prime to `p`.) -/

section AbelianizationQuot

variable {Γ : Type} [Group Γ] {p : ℕ}

/-- The closure `p̄` of the `p`-multiples in the additive abelianization `Γ^{ab}`. -/
noncomputable def pBarSub : AddSubgroup (Additive (Abelianization Γ)) :=
  AddSubgroup.closure {x : Additive (Abelianization Γ) | ∃ y : Additive (Abelianization Γ), p • y = x}

/-- The `p`-multiples lie in `p̄`. -/
theorem pBar_nsmul_mem (x : Additive (Abelianization Γ)) : p • x ∈ pBarSub (Γ := Γ) (p := p) :=
  AddSubgroup.subset_closure ⟨x, rfl⟩

/-- **The `p`-Frattini quotient of the abelianization**: `Γ^{ab} ⧸ p̄`. -/
abbrev zmodPQuot : Type := Additive (Abelianization Γ) ⧸ pBarSub (Γ := Γ) (p := p)

/-- **Every element of `Γ^{ab} ⧸ p̄` has order dividing `p`.**  The quotient-zero criterion
`QuotientAddGroup.eq_zero_iff` is stated in the *coercion* form `↑x = 0 ↔ x ∈ N`, which is why the
`mk'`-shaped rewrites miss; here `map_nsmul` is applied to the quotient map `mk'` first and the
coercion form is reached through `QuotientAddGroup.mk'_apply`. -/
theorem zmodPQuot_nsmul_eq_zero (x : zmodPQuot (Γ := Γ) (p := p)) : p • x = 0 := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (pBarSub (Γ := Γ) (p := p)) x
  rw [← map_nsmul (QuotientAddGroup.mk' (pBarSub (Γ := Γ) (p := p))) p y,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact pBar_nsmul_mem (Γ := Γ) (p := p) y

/-- **The `𝔽_p`-module structure on `Γ^{ab} ⧸ p̄`**: the quotient has exponent `p`, so it is a
`ZMod p`-module by `AddCommGroup.zmodModule`.  This is the coefficient side of
`h1loc_triv_card_abelianization` — the `𝔽_p`-dual of this module is what the locally constant
homomorphisms `↥H → 𝔽_p` are identified with. -/
noncomputable instance instModuleZmodPQuot : Module (ZMod p) (zmodPQuot (Γ := Γ) (p := p)) :=
  AddCommGroup.zmodModule (zmodPQuot_nsmul_eq_zero (Γ := Γ) (p := p))

/-- **Every additive hom `Γ^{ab} → 𝔽_p` descends to `Γ^{ab} ⧸ p̄`**: it kills all `p`-multiples
and hence the whole closure `p̄` (the target has exponent `p`).  This is the hypothesis
`p̄ ≤ ψ.ker` of `QuotientAddGroup.lift` — the first step of the forward direction of
`Z¹_c(↥H, 𝔽_p) ≃ₗ Dual (ZMod p) (↥H^{ab} ⧸ p̄)`. -/
theorem pBarSub_le_ker (ψ : Additive (Abelianization Γ) →+ ZMod p) :
    pBarSub (Γ := Γ) (p := p) ≤ ψ.ker := by
  rw [pBarSub, AddSubgroup.closure_le]
  rintro x ⟨y, rfl⟩
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_nsmul, nsmul_eq_mul, ZMod.natCast_self,
    zero_mul]

/-- **The additive hom `Γ^{ab} → 𝔽_p` induced by an additive hom `Γ → 𝔽_p`.**  Step (1) of the
forward direction of `Z¹_c(↥H, 𝔽_p) ≃ₗ Dual (ZMod p) (↥H^{ab} ⧸ p̄)`: a hom out of `Γ` into an
abelian group factors through the abelianization, by the universal property
`Abelianization.lift : (Γ →* A) ≃ (Abelianization Γ →* A)` — the additive bridge being
`Multiplicative.ofAdd` on values and `MonoidHom.toAdditive` on the hom itself. -/
noncomputable def abHom (φ : Γ → ZMod p) (hφ : ∀ g h : Γ, φ (g * h) = φ g + φ h) :
    Additive (Abelianization Γ) →+ ZMod p :=
  MonoidHom.toAdditive (Abelianization.lift
    { toFun := fun g => Multiplicative.ofAdd (φ g)
      map_one' := by
        have h1 : φ 1 = 0 := by
          have h := hφ 1 1
          rw [mul_one] at h
          exact add_left_cancel (by rw [h.symm, add_zero])
        show Multiplicative.ofAdd (φ 1) = 1
        rw [h1]
        rfl
      map_mul' := fun g h => by
        show Multiplicative.ofAdd (φ (g * h))
          = Multiplicative.ofAdd (φ g) * Multiplicative.ofAdd (φ h)
        rw [hφ g h]
        rfl })

/-- **The computation rule of `abHom`**: it restricts to `φ` along the canonical map
`Γ → Γ^{ab}`.  (`Abelianization.lift_apply_of` is the pointwise form of the universal property;
the `Multiplicative`/`Additive` bridges are `rfl`-level.) -/
theorem abHom_of (φ : Γ → ZMod p) (hφ : ∀ g h : Γ, φ (g * h) = φ g + φ h) (g : Γ) :
    abHom (p := p) φ hφ (Abelianization.of g) = φ g := by
  simp only [abHom, Abelianization.lift_apply_of]
  rfl

/-- **A syntactic handle for the quotient map `Γ^{ab} → Γ^{ab} ⧸ p̄`.**  `zmodPQuot` is an
`abbrev` over a quotient type-former, so coercions and rewrites do not see through it at argument
positions; naming the map (as was done for `B1Q`, `H1locLinearBwd` and `quotBotLinearEquiv`) gives
every downstream statement a handle that `simp`/`rw` can act on. -/
noncomputable def zmodPQuotMk :
    Additive (Abelianization Γ) →+ zmodPQuot (Γ := Γ) (p := p) :=
  QuotientAddGroup.mk' (pBarSub (Γ := Γ) (p := p))

/-- The defining equation of `zmodPQuotMk` on the canonical image of `Γ`. -/
@[simp] theorem zmodPQuotMk_of (g : Γ) :
    zmodPQuotMk (p := p) (Additive.ofMul (Abelianization.of g))
      = QuotientAddGroup.mk' (pBarSub (Γ := Γ) (p := p))
          (Additive.ofMul (Abelianization.of g)) := rfl

/-- **Step (2): the descent of an additive hom `Γ → 𝔽_p` to `Γ^{ab} ⧸ p̄`.**  Unconditional, since
every `𝔽_p`-valued hom kills `p̄` (`pBarSub_le_ker`). -/
noncomputable def quotHom (φ : Γ → ZMod p) (hφ : ∀ g h : Γ, φ (g * h) = φ g + φ h) :
    zmodPQuot (Γ := Γ) (p := p) →+ ZMod p :=
  QuotientAddGroup.lift (pBarSub (Γ := Γ) (p := p)) (abHom (p := p) φ hφ)
    (pBarSub_le_ker (p := p) (abHom (p := p) φ hφ))

/-- The computation rule of `quotHom` on representatives, through the handle `zmodPQuotMk`. -/
@[simp] theorem quotHom_mk (φ : Γ → ZMod p) (hφ : ∀ g h : Γ, φ (g * h) = φ g + φ h) (g : Γ) :
    quotHom (p := p) φ hφ (zmodPQuotMk (p := p) (Additive.ofMul (Abelianization.of g)))
      = φ g := by
  simp only [quotHom, zmodPQuotMk]
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk']
  exact abHom_of (p := p) φ hφ g

section QuotHomLin

variable [NeZero p]

/-- **Step (3): `quotHom` is `𝔽_p`-linear.**  The scalar action on any `ZMod p`-module is the
`val`-multiple (`Work.CohomologicalShrinking.naturalAlpha.psiLin_zmod_smul_eq_nsmul`, which holds
for an arbitrary `ZMod p`-module, so it applies to the quotient without unfolding `zmodModule`),
and `quotHom` is additive — `map_nsmul` bridges the two. -/
noncomputable def quotHomLin (φ : Γ → ZMod p) (hφ : ∀ g h : Γ, φ (g * h) = φ g + φ h) :
    zmodPQuot (Γ := Γ) (p := p) →ₗ[ZMod p] ZMod p where
  toFun := quotHom (p := p) φ hφ
  map_add' := map_add (quotHom (p := p) φ hφ)
  map_smul' c x := by
    rw [Work.CohomologicalShrinking.naturalAlpha.psiLin_zmod_smul_eq_nsmul (p := p) c x,
      map_nsmul,
      ← Work.CohomologicalShrinking.naturalAlpha.psiLin_zmod_smul_eq_nsmul (p := p) c
        (quotHom (p := p) φ hφ x),
      RingHom.id_apply]

/-- The computation rule of `quotHomLin`, inherited from `quotHom_mk`. -/
@[simp] theorem quotHomLin_mk (φ : Γ → ZMod p) (hφ : ∀ g h : Γ, φ (g * h) = φ g + φ h) (g : Γ) :
    quotHomLin (p := p) φ hφ (zmodPQuotMk (p := p) (Additive.ofMul (Abelianization.of g)))
      = φ g :=
  quotHom_mk (p := p) φ hφ g

/-- **Step (4): the converse.**  An `𝔽_p`-linear functional on `Γ^{ab} ⧸ p̄` restricts along
`Γ → Γ^{ab} → Γ^{ab} ⧸ p̄` to a function `Γ → 𝔽_p`. -/
noncomputable def homOfQuot (Ψ : zmodPQuot (Γ := Γ) (p := p) →ₗ[ZMod p] ZMod p) :
    Γ → ZMod p :=
  fun g => Ψ (zmodPQuotMk (p := p) (Additive.ofMul (Abelianization.of g)))

/-- The restriction of a functional is additive (so it is an additive hom `Γ → 𝔽_p`, the input
format of `abHom`/`quotHom`). -/
theorem homOfQuot_add (Ψ : zmodPQuot (Γ := Γ) (p := p) →ₗ[ZMod p] ZMod p) (g h : Γ) :
    homOfQuot (p := p) Ψ (g * h)
      = homOfQuot (p := p) Ψ g + homOfQuot (p := p) Ψ h := by
  simp only [homOfQuot, map_mul]
  rw [show Additive.ofMul (Abelianization.of g * Abelianization.of h)
        = Additive.ofMul (Abelianization.of g) + Additive.ofMul (Abelianization.of h) from rfl,
    map_add, map_add]

/-- **Step (5), first roundtrip**: restricting back to `Γ` undoes the passage to the quotient — the
composite `Γ → 𝔽_p` of `quotHomLin φ hφ` with `homOfQuot` is `φ` itself.  This is exactly the
computation rule `quotHomLin_mk`, since `homOfQuot` is *defined* as that composite. -/
theorem homOfQuot_quotHomLin (φ : Γ → ZMod p) (hφ : ∀ g h : Γ, φ (g * h) = φ g + φ h) (g : Γ) :
    homOfQuot (p := p) (quotHomLin (p := p) φ hφ) g = φ g :=
  quotHomLin_mk (p := p) φ hφ g

/-- **Step (5), second roundtrip on generators**: passing to the quotient and restricting back is the
identity on the canonical images of `Γ`.

The full statement for every element of `zmodPQuot` does **not** need induction over
`Abelianization` (the sweep confirmed `Abelianization.induction_on`, `Abelianization.induction` and
`Abelianization.lift_injective` are all absent from this tree).  The route is:
`Abelianization.lift` is an `Equiv`, so `Equiv.injective` together with `MonoidHom.ext` gives
`g = Abelianization.lift φm` as soon as `g ∘ Abelianization.of = φm` pointwise — which is exactly
this generator statement, applied to `g := Ψ ∘ zmodPQuotMk`; and then
`QuotientAddGroup.mk'_surjective` with `LinearMap.ext` lifts the equality from
`Additive (Abelianization Γ)` to `zmodPQuot`.  All four ingredients (`MonoidHom.ext`,
`AddMonoidHom.ext`, `LinearMap.ext`, `QuotientAddGroup.mk'_surjective`) are confirmed present. -/
theorem quotHomLin_homOfQuot_mk (Ψ : zmodPQuot (Γ := Γ) (p := p) →ₗ[ZMod p] ZMod p) (g : Γ) :
    quotHomLin (p := p) (homOfQuot (p := p) Ψ) (homOfQuot_add (p := p) Ψ)
        (zmodPQuotMk (p := p) (Additive.ofMul (Abelianization.of g)))
      = Ψ (zmodPQuotMk (p := p) (Additive.ofMul (Abelianization.of g))) := by
  rw [quotHomLin_mk]
  rfl

/-- The multiplicative hom out of `Γ^{ab}` corresponding to an additive hom out of
`Additive (Abelianization Γ)`: `x ↦ Multiplicative.ofAdd (h (Additive.ofMul x))`.  Built by a
structure literal (as `abHom` is) because `MonoidHom.toAdditive.symm` will not accept the merely
defeq codomain `ZMod p = Additive (Multiplicative (ZMod p))`. -/
noncomputable def toMulHom (h : Additive (Abelianization Γ) →+ ZMod p) :
    Abelianization Γ →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd (h (Additive.ofMul x))
  map_one' := by simp only [ofMul_one, map_zero, ofAdd_zero]
  map_mul' x y := by simp only [ofMul_mul, map_add, ofAdd_add]

@[simp] theorem toMulHom_apply (h : Additive (Abelianization Γ) →+ ZMod p)
    (x : Abelianization Γ) :
    toMulHom (p := p) h x = Multiplicative.ofAdd (h (Additive.ofMul x)) := rfl

/-- **Step (5), second roundtrip, full statement**: passing to the quotient and restricting back is
the identity, `quotHomLin (homOfQuot Ψ) (homOfQuot_add Ψ) = Ψ`.  The extension from the canonical
images of `Γ` to all of `zmodPQuot` uses `Abelianization.hom_ext` (agreement on
`Abelianization.of`'s image determines a hom out of `Γ^{ab}`) together with
`QuotientAddGroup.mk'_surjective`. -/
theorem quotHomLin_homOfQuot (Ψ : zmodPQuot (Γ := Γ) (p := p) →ₗ[ZMod p] ZMod p) :
    quotHomLin (p := p) (homOfQuot (p := p) Ψ) (homOfQuot_add (p := p) Ψ) = Ψ := by
  have h1 : toMulHom (p := p) (((quotHomLin (p := p) (homOfQuot (p := p) Ψ)
          (homOfQuot_add (p := p) Ψ)) : zmodPQuot (Γ := Γ) (p := p) →+ ZMod p).comp
            (zmodPQuotMk (p := p) (Γ := Γ)))
      = toMulHom (p := p) ((Ψ : zmodPQuot (Γ := Γ) (p := p) →+ ZMod p).comp
            (zmodPQuotMk (p := p) (Γ := Γ))) := by
    refine Abelianization.hom_ext _ _ ?_
    ext γ
    simp only [toMulHom_apply, MonoidHom.comp_apply, AddMonoidHom.comp_apply]
    exact quotHomLin_homOfQuot_mk (p := p) Ψ γ
  refine LinearMap.ext (fun x => ?_)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (pBarSub (Γ := Γ) (p := p)) x
  have h3 := congrFun (congrArg DFunLike.coe h1) (Additive.toMul y)
  simp only [toMulHom_apply, MonoidHom.comp_apply, AddMonoidHom.comp_apply] at h3
  exact Multiplicative.ofAdd.injective h3

end QuotHomLin

end AbelianizationQuot

/-! ## Node (1), trivial coefficients: the coboundaries vanish

With a trivially acting coefficient module, `d⁰ m` is the zero cochain (`g • m - m = 0`), so the
continuous coboundaries `B¹_c` vanish; hence so does the denominator `B1Q` of the local `H¹`, and
`finrank_H1loc_eq_finrank_quot` collapses `finrank H1loc` to the space of locally constant
homomorphisms `↥H → 𝔽_p` — the trivial-coefficient side `h1loc_triv_card_abelianization`. -/

section TrivialCoboundaries

variable {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [AddCommGroup M] [DistribMulAction Γ M]

/-- With a trivially acting coefficient module the continuous coboundaries vanish: `B¹_c = 0`. -/
theorem B1c_eq_bot_of_trivial (htriv : ∀ (g : Γ) (m : M), g • m = m) :
    Work.AbsoluteKummer.B1 Γ M = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  simp only [Work.AbsoluteKummer.B1, AddMonoidHom.mem_range] at hf
  obtain ⟨m, hm⟩ := hf
  rw [← hm, AddSubgroup.mem_bot]
  ext g
  simp only [Work.GroupCohomology.d0_apply, htriv, sub_self, Pi.zero_apply]

end TrivialCoboundaries

section TrivialQuot

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [IsAlgClosure k Ω]
  {H : Subgroup (Ω ≃ₐ[k] Ω)}

/-- For trivial coefficients the denominator of the local `H¹` vanishes. -/
theorem B1Q_triv_eq_bot :
    B1Q (p := p) (Γ := ↥H) (M := Work.SSGRoute.Triv p) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [mem_B1Q] at hx
  have hbot : Work.AbsoluteKummer.B1 ↥H (Work.SSGRoute.Triv p) = ⊥ :=
    B1c_eq_bot_of_trivial (Γ := ↥H) (M := Work.SSGRoute.Triv p) (fun _ _ => rfl)
  rw [hbot, AddSubgroup.mem_bot] at hx
  exact Subtype.ext hx


/-- The quotient of a module by the zero submodule is the module itself.  (`Submodule.quotientBot`
is not available in this tree, so the linear equivalence is built by hand: `mkQ ⊥` is bijective
(`ker_mkQ` and `mkQ_surjective`), and the equivalence is its inverse.) -/
noncomputable def quotBotLinearEquiv (R : Type*) [Ring R] (V : Type*) [AddCommGroup V]
    [Module R V] : (V ⧸ (⊥ : Submodule R V)) ≃ₗ[R] V :=
  (LinearEquiv.ofBijective (Submodule.mkQ (⊥ : Submodule R V))
    ⟨LinearMap.ker_eq_bot.mp (Submodule.ker_mkQ (⊥ : Submodule R V)),
      Submodule.mkQ_surjective (⊥ : Submodule R V)⟩).symm

/-- **The trivial-coefficient side of node (1)**: `finrank H1loc(D_A, 𝔽_p)` is the `𝔽_p`-dimension
of the locally constant homomorphisms `D_A → 𝔽_p` — the continuous `1`-cocycles `Z¹_c(↥H, 𝔽_p)`
with trivial coefficients.  The coboundaries vanish (`B1Q_triv_eq_bot`), so the quotient form of
the model bridge `finrank_H1loc_eq_finrank_quot` collapses. -/
theorem finrank_H1loc_triv :
    Module.finrank (ZMod p) (H1loc p k Ω K (Work.SSGRoute.Triv p) H)
      = Module.finrank (ZMod p) ↥(Work.AbsoluteKummer.Z1 ↥H (Work.SSGRoute.Triv p)) := by
  rw [finrank_H1loc_eq_finrank_quot (p := p) (k := k) (Ω := Ω) (K := K) (H := H)
    (M := Work.SSGRoute.Triv p) (fun _ _ => rfl)]
  rw [B1Q_triv_eq_bot (p := p) (H := H)]
  exact LinearEquiv.finrank_eq (quotBotLinearEquiv (ZMod p)
    ↥(Work.AbsoluteKummer.Z1 ↥H (Work.SSGRoute.Triv p)))

end TrivialQuot

/-! ## The trivial-coefficient case: classes in `H1loc(D_A, 𝔽_p)` are the values on `D_A`

First step of the node `h1loc_triv_card_abelianization` (see the three-node plan below): with
`M = Triv p = 𝔽_p` the action is trivial, so by
`Work.SSGRoute.PT.mem_coboundaries_iff` the `1`-coboundaries on `H` are exactly the functions
vanishing on `H`, and therefore two locally constant cocycles have the same class in
`H1loc(·, 𝔽_p)` exactly when they agree on `H`.  The model bridge
`Work.SSGRoute.H1locEquivH1` (`LTDDefs/H1loc_iso_H1cont.lean`, proved) identifies `H1loc` with the
workspace's continuous-cochain model `Work.AbsoluteKummer.H1`, in which `B1(G, 𝔽_p) = 0`; so the
class criterion below *is* the identification `H1loc(D_A, 𝔽_p) = Hom_cont(D_A, 𝔽_p)` once that
bridge is upgraded from additive to linear. -/

section TrivCase

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {H : Subgroup (Ω ≃ₐ[k] Ω)}

/-- With the trivial coefficient module `𝔽_p`, the `1`-coboundaries on `H` are the functions
vanishing on `H` (`mem_coboundaries_iff` of `PT/h1loc_finrank_trivialAction.lean`). -/
lemma mem_coboundaries_triv {f : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.Triv p} :
    f ∈ coboundaries p k Ω K (Work.SSGRoute.Triv p) H ↔ ∀ g ∈ H, f g = 0 :=
  Work.SSGRoute.PT.mem_coboundaries_iff p k Ω K (Work.SSGRoute.Triv p) H (fun _ _ => rfl) f

/-- The submodule of the locally constant `𝔽_p`-cocycles that is quotiented out in `H1loc`
(so that `H1loc p k Ω K (Triv p) H = ↥(lcCocycles …) ⧸ trivDenom K H` definitionally). -/
abbrev trivDenom (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Submodule (ZMod p) ↥(lcCocycles p k Ω K (Work.SSGRoute.Triv p) H) :=
  Submodule.comap (lcCocycles p k Ω K (Work.SSGRoute.Triv p) H).subtype
    (coboundaries p k Ω K (Work.SSGRoute.Triv p) H)

/-- **The class criterion for trivial coefficients**: two locally constant `1`-cocycles with values
in `𝔽_p` define the same class in `H1loc(·, 𝔽_p)` exactly when they agree on `H`.  In particular
`H1loc(D_A, 𝔽_p)` is a quotient of the space of locally constant *homomorphisms* `D_A → 𝔽_p`,
i.e. of `Hom_cont(D_A, 𝔽_p)`. -/
lemma H1loc_triv_mk_eq_iff
    (f f' : ↥(lcCocycles p k Ω K (Work.SSGRoute.Triv p) H)) :
    (Submodule.Quotient.mk (p := trivDenom (p := p) (k := k) (Ω := Ω) K H) f
        : H1loc p k Ω K (Work.SSGRoute.Triv p) H)
      = Submodule.Quotient.mk (p := trivDenom (p := p) (k := k) (Ω := Ω) K H) f'
      ↔ ∀ g ∈ H, f.1 g = f'.1 g := by
  rw [Submodule.Quotient.eq (p := trivDenom (p := p) (k := k) (Ω := Ω) K H),
    Submodule.mem_comap, mem_coboundaries_triv]
  constructor
  · intro h g hg
    have h0 : (f - f').1 g = 0 := h g hg
    simpa using sub_eq_zero.mp h0
  · intro h g hg
    have h0 : f.1 g = f'.1 g := h g hg
    simpa [h0]

end TrivCase

/-! ## The three-node plan for `kummerBaseDim` (recorded 2026-09-26)

`kummerBaseDim` is the μ_p-case dimension equality of local Tate duality.  The workspace's own
vocabulary file `Submission/Work/SSGRoute/mup_local_defs.lean` (definitions proved there:
`mup.decompField k Ω A = Ω^{D_A}`, `mup.KummerGroup p F = Fˣ ⧸ (Fˣ)^p`, `mup.TrivMod p G`) names
the intended reduction of this equality into *three* nodes, none of which is on disk yet:

1. **`h1loc_triv_card_abelianization`** — the trivial-coefficient side.  With `M = Triv p` the
   action is trivial, so `coboundaries` is the set of functions vanishing on `D_A`
   (`mem_coboundaries_iff`, proved in
   `Submission/Work/SSGRoute/PT/h1loc_finrank_trivialAction.lean`) and
   `H1loc(D_A, 𝔽_p) = Hom_cont(D_A, 𝔽_p)`, whose `𝔽_p`-dimension is the `p`-Frattini rank of the
   abelianization `D_A^{ab}`, i.e. `dim (D_A^{ab} ⧸ (D_A^{ab})^p)`: a continuous homomorphism
   `D_A → 𝔽_p` factors through `D_A^{ab}` and kills `p`-th powers, and conversely.

   *Status (2026-09-26, after the third stretch).*  The case is now cut into three pieces, of which
   the first two are formal:
   (1a) the class criterion for trivial coefficients — **proved below** (`mem_coboundaries_triv`,
       `H1loc_triv_mk_eq_iff`): classes are the values on `H`; the surjectivity of "restrict to
       `H`" (i.e. the fact that every locally constant hom on `H` extends) is already on disk as
       the **proved model bridge** `Work.SSGRoute.H1locEquivH1`
       (`LTDDefs/H1loc_iso_H1cont.lean`: `H1loc p k Ω K M H ≃+ Work.AbsoluteKummer.H1 ↥H M`,
       built from `restrictCocycle`/`extendCocycle`).  The remaining formal gap is that this bridge
       is stated **additively** (`≃+`); a linear upgrade (`≃ₗ`, e.g. by re-running its proof with
       `Submodule.mapQ`) is what makes it usable for `Module.finrank`.
   (1b) `Work.AbsoluteKummer.H1 G 𝔽_p = Hom_cont(G, 𝔽_p)`: in that model
       `Z1 G M = Work.GroupCohomology.Z1 G M ⊓ C1c G M` and `B1 G M = (d0 G M).range`
       (`AbsoluteKummer/Defs.lean`), so for trivial coefficients `B1 = 0` and `Z1` is the set of
       locally constant homomorphisms.
   (1c) `Hom_cont(G, 𝔽_p) = Dual (ZMod p) (G^{ab} ⧸ (G^{ab})^{p-closure})` — a continuous
       homomorphism into a group of exponent `p` factors through the abelianization and kills
       `p`-th powers — and then `Module.finrank (Dual (ZMod p) W) = Module.finrank W` is
       **Mathlib's `Subspace.dual_finrank_eq`, which carries no finiteness hypothesis**: for
       infinite-dimensional `W` both sides are `0` (as `Module.finrank` is `0` on an
       infinite-dimensional space).  So once (1c) is set up, the dimension statement is free and
       needs neither finiteness nor LCFT; the arithmetic enters only through node (3), which
       supplies the *identification of the two ranks*.
2. **`h1loc_mup_card_kummer`** — the `μ_p`-coefficient side: Kummer theory for the profinite group
   `D_A` over the decomposition field `mup.decompField k Ω A = Ω^{D_A}` (whose absolute Galois
   group is `D_A`, the stabiliser of a place being closed), giving
   `H1loc(D_A, μ_p) ≅ mup.KummerGroup p (Ω^{D_A})` (`Ω` algebraically closed, so the `p`-power map
   on `Ωˣ` is onto and Hilbert 90 supplies the Kummer isomorphism).
3. **`local_reciprocity_mod_p_frattini_rank`** — the *arithmetic* input: local Artin reciprocity
   modulo `p` for the completion of `k` at the finite prime below `A`, i.e. that the `p`-Frattini
   ranks of `D_A^{ab}` and of `Ω^{D_A,×} ⧸ (Ω^{D_A,×})^p` agree (both are
   `k_v^× ⧸ (k_v^×)^p` up to the identification of `Ω^{D_A}` with the algebraic closure of `k`
   inside `k_v`).  This is the `μ_p`-case face of `NK.NUV2.kernelCondition_all` (local reciprocity
   in kernel form plus the Frattini quotient of `G_{k_v}^{ab}`).

Together, (1)–(3) give `kummerBaseDim`, hence `localKummer_base`, hence one of the two ingredients
of `localTatePairing_canonical` / `E7`.  The formal work of (1) (the `Hom_cont` identification) is
available now; (2) uses the Kummer/Hilbert-90 library of `Submission/Work/AbsoluteKummer/`; (3) is
the genuine local CFT input. -/

/-- **The pure Kummer input of the base case** (local class field theory + Hilbert 90): at a finite
place `A`, the local `H¹` with coefficients in `𝔽_p` and with coefficients in the cyclotomic module
`μ_p = DualMod p T` have the same `𝔽_p`-dimension, because

  `H¹(k_v, 𝔽_p) = Hom_cont(k_v^×, 𝔽_p) ≅ (k_v^× ⧸ (k_v^×)^p)^∨` and `H¹(k_v, μ_p) ≅ k_v^× ⧸ (k_v^×)^p`

by local Kummer theory and local class field theory (`NK.NUV2.kernelCondition_all`, local
reciprocity in kernel form, together with Hilbert 90 for `D_A`).  See the three-node plan above
(`h1loc_triv_card_abelianization`, `h1loc_mup_card_kummer`,
`local_reciprocity_mod_p_frattini_rank`). -/
theorem kummerBaseDim
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Module.finrank (ZMod p)
        (Work.SSGRoute.H1loc p k Ω K (Work.SSGRoute.Triv p) (SSGRoute.decomp k A))
      = Module.finrank (ZMod p)
          (Work.SSGRoute.H1loc p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A)) := by
  sorry

/-- **Local Kummer, base case of E7.**  At every place `A` of `Ω` over a finite prime of `k`, the
local `H¹` with coefficients in the trivial module `𝔽_p` and with coefficients in its Tate dual
`μ_p = DualMod p (𝔽_p ⊗ T)` have the same dimension over `𝔽_p` (Kummer: `H¹(k_v, μ_p) ≅ k_v^×/(k_v^×)^p`,
and `H¹(k_v, 𝔽_p) = Hom(G_v, 𝔽_p) ≅ (k_v^×/(k_v^×)^p)^∨`). -/
theorem localKummer_base
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Module.finrank (ZMod p)
        (Work.SSGRoute.H1loc p k Ω K (Work.SSGRoute.Triv p) (SSGRoute.decomp k A))
      = Module.finrank (ZMod p)
          (Work.SSGRoute.H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) (Work.SSGRoute.Triv p) T))
            (SSGRoute.decomp k A)) := by
  -- reduce the second coefficient module `DualMod p (Triv p ⊗ T)` to `DualMod p T`
  rw [← finrank_H1loc_eq_of_equiv (K := K) (H := SSGRoute.decomp k A)
    (e := dualEquiv trivTensorEquiv)
    (dualEquiv_smul trivTensorEquiv trivTensorEquiv_smul)]
  -- the remaining equality is the Kummer input
  exact kummerBaseDim p k Ω K ζ hζ hζK T hT A hA

end

end Work.SSGRoute.PTembedding

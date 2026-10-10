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
import Submission.Work.SSGRoute.E9c.TransportDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-existence input of node `C6`

This file contains **one arithmetic statement** — `exists_regularModule_inert_level` — which is
exactly the input that the route recorded in `Submission/Work/SSGRoute/SSGStage/unramifiedDetector.lean`
("The *regular-module level*: a complete route with one arithmetic input") needs, and nothing else.
It is stated in the vocabulary of `SSGRoute.PTExt` (`galRes`, `decompK`), so that its consumer can
use it directly.  The body is deliberately left as a `sorry`: what follows is the mathematical
content that has to be supplied.

## What is asked

`L ⊇ K`, finite Galois over `k`, a place `q' | q` of `L`, such that

1. `e(q'|q) = 1` (so the `p`-coprimality clause of the node's conclusion holds);
2. ~~`q` is *inert* in `L/K`~~ — **this clause is impossible and has been removed; see the
   correction below.**  What is asked instead is a statement about the *coordinates* of the
   decomposition group with respect to a splitting `s` of `galRes k K L`:
   (a) the inertia `I^{L/k}_{q'}` has trivial coordinates (`coordKer γ = 1`), and
   (b) some `d ∈ decompK q'` has coordinate the *basis element at the identity*,
   `e (coordKer d) =` the indicator function of `1 ∈ Gal(K/k)`.
3. `N` is the **regular** `Gal(K/k)`-module: there is a group isomorphism
   `e : N ≃* Multiplicative (Gal(K/k) → ZMod p)` intertwining the conjugation action of
   `Gal(L/k)` on `N` (through `galRes`) with the left-regular action on functions.

## Correction (found while writing this file): inertness is impossible

"`q` inert in `L/K`" would say that the decomposition group `D_{q'}(L/K)` has order
`e·f = f = [L:K] = |N|`.  But `L/K` unramified at `q'` (`e = 1`) makes `D_{q'}(L/K)` the
Galois group of a residual extension generated by the Frobenius, hence **cyclic**; and
`N ≅ 𝔽_p[G₀] = (ℤ/p)^{|G₀|}` is elementary abelian, cyclic only if `|G₀| = 1`.  So for `G₀ ≠ 1`
the conditions "`|N| = p^{|G₀|}`" and "`D_{q'} ∩ N = N`" are mutually exclusive, and the earlier
form of this statement (which demanded `N ≤ decompK q'`) was false.  The conclusion above keeps
only the two coordinate conditions (a), (b), which are what the detection actually consumes.

## Why this suffices (group-theoretic half, all provable)

* `N ≅ 𝔽_p[G₀]` is *induced from the trivial subgroup* (`G₀ = Gal(K/k)`), hence
  `H²(G₀, N) = H²(1, 𝔽_p) = 0` by Shapiro: the extension `1 → N → Gal(L/k) → G₀ → 1`
  **splits automatically**, and `Hom_{G₀}(N, M) ≅ M` for *every* `G₀`-module `M`
  (the element `m` corresponds to `φ_m(δ_γ) = γ·m`, where `δ_γ` is the basis element indexed
  by `γ`).
* For a splitting `s` and every `G₀`-equivariant `φ : N → M` (with `N` acting trivially on `M`),
  the formula `γ ↦ φ (coordKer γ)` is a `1`-cocycle on `Gal(L/k)` with values in `M`
  (`mem_cocycles_coordKer`); the cocycle identity is additivity of `φ` plus its
  `G₀`-equivariance, and `coordKer` is the `N`-coordinate of `γ` relative to `s`.
* **Detection.**  By (2b), some `d ∈ D_{q'}` has `coordKer d = δ_1 := e⁻¹(indicator of 1)`, and
  then `μ (h_m d) = μ (φ_m δ_1) = μ (1·m) = μ m ≠ 0` for `m` with `μ m ≠ 0`.  Here
  `μ : res_{D_w} M ⟶ ℚ/ℤ` is the functional dual to `φ` (Local Tate duality,
  `divRep_detecting_class`) and the level pairing evaluates it
  (`Work.SSGRoute.E7cOmega.levelPair_ratDivSES_mk0_ne_zero_iff`).  Note that *no* inertness is
  needed for this step: only the single element `d` and its coordinate matter.
* **Unramifiedness.**  By (2a) every inertia element has trivial coordinate, so
  `h_m` vanishes on `I^{L/k}_{q'}`; when `K/k` is unramified at `q` this condition is what (2a)
  records, and when `I_w ≠ 1` it is exactly the vanishing of the inertia graph
  `{(v σ, σ) : σ ∈ I_w}` that the earlier analysis asked for.

## Ingredients for the proof (all arithmetic, none of it group cohomology)

* **Kummer theory over `K(ζ_p)`.**  A level may be taken to contain `K(ζ_p)`, which is
  unramified at `q` because `p ∉ q`.  Choose `α ∈ Kˣ` whose conjugates `σ(α)` (`σ ∈ G₀`) are
  independent in `Kˣ/Kˣ^p`; then `Δ := ⊕_σ 𝔽_p·σ(α)` is the regular `G₀`-module and
  `L := K(ζ_p)(δ^{1/p} : δ ∈ Δ)` is Galois over `k` with
  `Gal(L/K(ζ_p)) ≅ Hom(Δ, μ_p) ≅ 𝔽_p[G₀]` (the `G₀`-action permutes the generators, so the
  `Gal(L/K)`-part is regular after quotienting by the cyclotomic layer).  Relevant on-disk
  material: `Submission.Work.KummerRealization.*` (Scholz's radical construction
  `A ⋊ (ℤ/n)ˣ`, the Kummer duality `Gal(L/k) ≅ Hom(Δ,μ_n)`, `scholzField`),
  `NK.LocalAnabelian.kummerField`, and the `Submission.Work.Kummer*` chapter.
* **Local control at the places above `q ∩ k`.**  The local class of `σ(α)` at `q` is the
  `σ`-transport of the local class of `α` at `σ⁻¹(q)`, so *all* local conditions at the finitely
  many places above `q ∩ k` can be prescribed at once by the **proved, axiom-clean** Grünwald
  input `Work.SSGRoute.GrunwaldWang.isKummerSurjective_nat`
  (`Kˣ/(Kˣ)^n ↠ ∏_𝔮 K_𝔮ˣ/(K_𝔮ˣ)^n`, every number field, every modulus) — choose `α` to be a
  *unit* at all of them (so `e(q'|q) = 1`) whose local classes span the full unramified
  `𝔽_p`-space at `q` (so the decomposition group is all of `N`, i.e. `q` is inert).
* **The local Kummer–Frobenius dictionary** converting the local classes of the `σ(α)` at `q`
  into the decomposition group `D_{q'}(L/K) = N` and the inertia graph `v`.

Nothing in this file is proved; it is the single named arithmetic input of the node.
-/

namespace Work.SSGRoute.SSGStage

/-- **Conjugation lands in the kernel of `galRes`**: the kernel of `galRes k K L` is normal, and
this is the membership proof used to state the equivariance of the regular-module isomorphism
below. -/
theorem ker_galRes_conj_mem (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) (σ : ↥L ≃ₐ[k] ↥L)
    (g : (SSGRoute.PTExt.galRes k K ↥L).ker) :
    σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹ ∈ (SSGRoute.PTExt.galRes k K ↥L).ker := by
  show SSGRoute.PTExt.galRes k K ↥L (σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹) = 1
  rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp g.property, mul_one]
  exact mul_inv_cancel _

/-- **The `N`-coordinate of an element of `Gal(L/k)` relative to a splitting `s`.**  For a section
`s : Gal(K/k) →* Gal(L/k)` of `galRes k K L` (a splitting of the extension
`1 → N → Gal(L/k) → Gal(K/k) → 1`, which exists as soon as `N` is the regular
`Gal(K/k)`-module, since then `H²(Gal(K/k), N) = 0` by Shapiro), the element
`γ * (s (galRes γ))⁻¹` lies in `N = ker (galRes)`.

This is the first coordinate of the construction of the detecting class: for a
`Gal(K/k)`-equivariant `φ : N →+ M.V`, the map `γ ↦ φ (coordKer L s hs γ)` is the
`1`-cocycle `h` of the level-pairing computation in `SSGStage/unramifiedDetector.lean`. -/
noncomputable def coordKer (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (γ : ↥L ≃ₐ[k] ↥L) :
    (SSGRoute.PTExt.galRes k K ↥L).ker :=
  ⟨γ * (s (SSGRoute.PTExt.galRes k K ↥L γ))⁻¹, by
    show SSGRoute.PTExt.galRes k K ↥L (γ * (s (SSGRoute.PTExt.galRes k K ↥L γ))⁻¹) = 1
    rw [map_mul, map_inv, hs]
    exact mul_inv_cancel _⟩

@[simp] theorem coordKer_coe (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (γ : ↥L ≃ₐ[k] ↥L) :
    (coordKer k K Ω L s hs γ : ↥L ≃ₐ[k] ↥L)
      = γ * (s (SSGRoute.PTExt.galRes k K ↥L γ))⁻¹ := rfl

/-- **The level-existence input of node `C6`** (all regimes, including `p ∣ |I_w|`).

**WARNING (2026-10-02): THIS STATEMENT IS FALSE.**  The conjunction of the coboundary clause and
the detecting-coordinate clause `e (coordKer d) = δ₁` is unsatisfiable whenever `p ∣ |I_w|` (and the
trivial-coordinates variant is unsatisfiable whenever `I_w ≠ 1`).  See §(3) of the session findings
in `SSGStage/unramifiedDetector.lean`: conjugating an inertial `γ` by `d` forces
`e (n + n₀ - (galRes d) ▷ n₀)` (where `n = coordKer d`) to be fixed by the left-regular
`I_w`-action, while its coordinate sum is `1` and every `I_w`-coset-constant vector has sum divisible
by `|I_w|`; witness `k = ℚ`, `K = ℚ(√3)`, `p = 2`, `q = (√3)`.  Do not attempt to prove it.  The
correct inputs are `SSGRoute/SSGStage/exists_regularModuleLevel_iso` (the bare regular level, no
coordinate clause) together with `SSGRoute/SSGStage/inertiaGraph_coboundary` and the coordinate
analysis recorded in `SSGStage/unramifiedDetector.lean`. -/


theorem exists_regularModule_level (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal)) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w),
      q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
      ∃ e : (SSGRoute.PTExt.galRes k K ↥L).ker ≃*
          Multiplicative ((K ≃ₐ[k] K) → ZMod p),
        (∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
          e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹, ker_galRes_conj_mem p k K Ω L σ g⟩ =
            Multiplicative.ofAdd (fun τ : K ≃ₐ[k] K =>
              Multiplicative.toAdd (e g) ((SSGRoute.PTExt.galRes k K ↥L σ)⁻¹ * τ))) ∧
        ∃ (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
          (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
          (n₀ : (SSGRoute.PTExt.galRes k K ↥L).ker),
          (∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
            (coordKer k K Ω L s hs γ : ↥L ≃ₐ[k] ↥L)
              = s (SSGRoute.PTExt.galRes k K ↥L γ) * (n₀ : ↥L ≃ₐ[k] ↥L)
                  * (s (SSGRoute.PTExt.galRes k K ↥L γ))⁻¹ * (n₀ : ↥L ≃ₐ[k] ↥L)⁻¹) ∧
          ∃ d : ↥L ≃ₐ[k] ↥L,
              d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
              ∃ v : (K ≃ₐ[k] K) → ZMod p, v 1 = 1 ∧
                (∀ τ : K ≃ₐ[k] K, τ ≠ 1 → v τ = 0) ∧
                e (coordKer k K Ω L s hs d) = Multiplicative.ofAdd v := by
  sorry

-- ## Ramified case: what the coordinate analysis gives, and where it stops (2026-10-02)
--
-- Let `I_w = I^{K/k}_q` and `I = I^{L/k}_{q'}`.  With `e(q'|q) = 1` one has `I ≅ I_w` via
-- `galRes`.  Two facts, both from the coordinate formula `coordKer γ = γ · (s (galRes γ))⁻¹`:
--
-- * If the inertia graph vanishes for the chosen splitting (`coordKer γ = 1` for `γ ∈ I`), then
--   the detecting class `h_m γ = φ_m (coordKer γ)` vanishes on `I` and no further condition on
--   `m` is needed: the inertia condition of the level pairing is *automatic*.
--   (Equivalently: the graph of the inertia is the coboundary `σ ↦ σ ▷ n₀ · n₀⁻¹`, and
--   `φ_m (σ ▷ n₀ · n₀⁻¹) = (σ - 1) · φ_m n₀ = 0` because `I_w` acts trivially on `M` by `hI`.)
-- * For `d ∈ decompK q'` with coordinate `n = coordKer d` and `γ = s(σ₀)` (`σ₀ ∈ I_w`), one has
--   `coordKer (d γ d⁻¹) = n · (τ ▷ n)⁻¹` with `τ = galRes d · σ₀ · (galRes d)⁻¹ ∈ I_w`.  The
--   vanishing of the inertia graph therefore FORCES `τ ▷ n = n`: the detection coordinate must be
--   `I_w`-invariant.  Moreover, for the detection to be readable off `μ` alone one wants `n`
--   supported in `D_w`; then `φ_m n = (Σ_{γ ∈ D_w} c_γ) · m` and the detection value is
--   `(Σ_{γ ∈ D_w} c_γ) • μ m`, non-zero as soon as `Σ_{γ ∈ D_w} c_γ ≠ 0`.
--
-- **Where it stops.**  If `p ∣ |I_w|` (possible with `p ∉ q`, e.g. `k = ℚ`, `p = 3`,
-- `K = ℚ(2^{1/3})`, `q = (2)`, where `e(q|q∩k) = 3`), then every `I_w`-invariant function
-- supported in `D_w` has total coefficient `0` in `𝔽_p` (it is constant on the `I_w`-cosets, each
-- of size divisible by `p`).  So no detection coordinate of that kind exists, and in that regime
-- the class `h_m` built from `Hom_{G₀}(N, M) ≅ M` alone cannot detect: the argument has to use
-- coordinates outside `D_w` (whose `μ`-values are not controlled by `hI`), or a different class in
-- `H¹(Gal(L/k), res M)` altogether.  The statement proved to suffice below is the
-- `p ∤ |I_w|` case; the `p ∣ |I_w|` case is open here.
--
-- ## On-disk consumers of this file
--
-- * `Submission/Work/SSGRoute/HSRow/regularModule_extension_splits.lean` — the splitting `s`
--   exists as soon as `ker (galRes) ≅ 𝔽_p[Gal(K/k)]` (with `Function.Surjective π`, which holds for
--   `galRes`); reviewers showed the surjectivity hypothesis is *necessary* there.
-- * `Submission/Work/SSGRoute/HSRow/detectingFunctional_of_regularModuleLevel.lean` — the
--   group-theoretic assembly step from this file's datum to the detecting functional `φ`
--   (its helper `regular_functional_equivariant` is proved; the assembly theorem is in progress).

/-!
## Decomposition of the level datum into dispatchable pieces (2026-10-02)

The statement above is the only remaining `sorry` of this lane.  It splits into three pieces; the
arithmetic ones reduce to `Work.SSGRoute.GrunwaldWang.isKummerSurjective_nat` (proved, axiom-clean)
and to the Kummer material under `Submission.Work.KummerRealization` / `Work.Kummer`, while the
bookkeeping in the level's own vocabulary is held here.

* **D1 — the module structure (Kummer realisation).**  From `k`, `K`, `p`: a level `L ⊇ K`, finite
  Galois over `k`, with a `Gal(K/k)`-equivariant group isomorphism
  `ker (galRes k K L) ≃* Multiplicative (Gal(K/k) → ZMod p)` (the *regular* module).  This is the
  clause forced to have `[L:K] = p^{|K:k|}`; the caveat is Reviewer 1's: Kummer theory over `K(ζ_p)`
  overshoots by `[K(ζ_p):K]`, so this piece needs a Kummer *descent* (or a base containing `μ_p`,
  with the resulting `Gal(L/K)` compared back).  Material: `Work.KummerRealization.*`
  (`scholzField`, the Kummer duality `Gal(L/k) ≅ Hom(Δ,μ_n)`), `NK.LocalAnabelian.kummerField`.
* **D2 — the local conditions at `q`.**  Given a Kummer datum (`α ∈ Kˣ` with independent conjugates,
  units at the places above `q ∩ k`): arrange `e(q'|q) = 1`, the coboundary clause for the inertia,
  and the `δ₁`-coordinate of a decomposition element.  All of the local prescriptions at the finitely
  many places above `q ∩ k` are supplied at once by `isKummerSurjective_nat` (the local class of
  `σ(α)` at `q` is the `σ`-transport of the local class of `α` at `σ⁻¹(q)`), together with the local
  Kummer–Frobenius dictionary converting those classes into `D_{q'}(L/K)` and the inertia graph.
* **D3 — the coboundary bookkeeping (held here).**  Translating the Kummer description of the level
  into the five clauses of the statement (`e` and its equivariance, `s` and `hs` — on disk as
  `HSRow/regularModule_extension_splits` — `n₀` and the inertia coboundary, and the `δ₁`-coordinate
  of `d`).

Consumer-side: the two halves the level datum feeds are both proved —
`SSGStage/extHRestrict_eCoh_coordKer_eq_zero` (unramifiedness, no hypothesis on `M`) and
`SSGStage/levelPair_eCoh_cocycles_ne_zero` (non-vanishing of the pairing, stated at the
`D_{q'}`-module so that the criterion fires directly).
-/

/-!
### D2: a local constraint that the dispatch statement must carry (2026-10-02)

`e(q'|q) = 1` makes `L_{q'} / K_q` an *unramified* extension whose Galois group is
`D_{q'}(L/K) ⊆ N`, and `N ≅ 𝔽_p[G₀]` has exponent `p`.  The maximal unramified abelian extension of
a local field is `K_q^{ur}` with group `Ẑ`, whose `p`-part is `ℤ_p`; hence the maximal unramified
`p`-elementary extension of `K_q` has **rank one**, i.e.

  `e(q'|q) = 1  ⟹  |D_{q'}(L/K)| ≤ p`  (and `D_{q'}(L/K)` is cyclic).

So D2 cannot prescribe arbitrary local classes: the classes of the conjugates `σ(α)` at `q` must span
a subspace of the *unramified* part of `K_qˣ/(K_qˣ)^p` of rank at most one, and the whole
`p`-torsion of `D_{q'}(L/K)` must come from that one class.  (Equivalently: in the Kummer dictionary
the inertia is trivial at `q'` exactly when the prescribed local classes lie in
`𝒪_qˣ·(K_qˣ)^p` and are pairwise dependent modulo the "1-unit" part — a check the D2 prover must run
before choosing the prescription.)  This is the local half of the `σ`-transport formulation:
the local class of `σ(α)` at `q` is the `σ`-transport of the local class of `α` at `σ⁻¹(q)`, so the
prescription is made at the places above `q ∩ k` and the *decomposition group* is read off from it.

This is compatible with (and in fact complements) the coboundary clause: with `I^{L/K}_{q'} = 1` the
inertia coboundary lives in the `K/k`-part and the `δ₁`-coordinate must be an element of the
order-`≤ p` cyclic group `D_{q'}(L/K) ⋊ D_w` — no inertness of `q` in `L/K` is required anywhere.
-/

/-!
## The Kummer datum (vocabulary for D1/D2)

The structure `KummerDatum` records the *data* from which the level of `exists_regularModule_level`
is built: a Kummer generator `α ∈ Kˣ` together with the level `L ⊇ K` it generates and the place
`q' | q`.  Only the fields that can be stated without any Kummer theory are fields here; the
*assertions* about them (that `L` is generated by the `p`-th roots of the conjugates of `α`, that the
conjugates are `𝔽_p`-independent modulo `p`-th powers, that the prescribed local classes are the
local classes of `α`, and that the resulting decomposition group is the one wanted) are precisely the
three pieces D1/D2/D3 recorded above, each of which states one of them.  Keeping the assertions out
of the structure is what makes them separately statable and separately dispatchable.
-/
structure KummerDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) where
  /-- The Kummer generator. -/
  α : Kˣ
  /-- The level it generates. -/
  L : IntermediateField K Ω
  /-- The level is a number field. -/
  numberField : NumberField ↥L
  /-- The level is finite over the base. -/
  finiteDimensional : FiniteDimensional k ↥L
  /-- The level is Galois over the base. -/
  isGalois : IsGalois k ↥L
  /-- The place of `L` above `q`. -/
  q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L)
  /-- `q'` lies above `q`. -/
  liesOver : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
    (NK.GlobalCFT.Place.ofFinite q)
  /-- The ramification index of `q'` over `q` is one (the clause D2 must deliver). -/
  e_eq_one : q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1
  /-- The local `p`-classes prescribed at the places of `K`; the D2 prover's obligation is that
  these are realised by the conjugates of `α` (the `σ`-transport) and that their span is the
  unramified subspace of rank at most one recorded in the D2 note. -/
  localClass : Kˣ → Prop
  /-- The local prescriptions are nonempty. -/
  localClass_nonempty : localClass α

attribute [instance] KummerDatum.numberField KummerDatum.finiteDimensional KummerDatum.isGalois

end Work.SSGRoute.SSGStage

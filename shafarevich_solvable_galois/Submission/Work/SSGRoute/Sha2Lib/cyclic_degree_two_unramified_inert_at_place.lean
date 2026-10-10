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
import Submission.Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg
import Submission.NK.NUV2.LC.adjoinSq_normal_finrank_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField IntermediateField
open Polynomial
open IsDedekindDomain.HeightOneSpectrum

namespace Work.SSGRoute.Sha2Lib

/-- A finite-dimensional extension of a field of characteristic zero of dimension at most two is
Galois: it is separable (characteristic zero) and normal because every minimal polynomial has
degree at most two and a polynomial of degree at most two with a root splits. -/
theorem isGalois_of_finrank_le_two {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [CharZero K] (h : Module.finrank K E ≤ 2) : IsGalois K E :=
  isGalois_iff.mpr ⟨Algebra.IsSeparable.of_integral K E, NK.NUV2.LC.normal_of_finrank_le_two h⟩

/-- **The local computation: a degree-`2` polynomial with irreducible reduction at `Q` gives
`e(w|Q) = 1`, `f(w|Q) = 2` for every prime `w` of `𝓞 M` above `Q`.**

Let `M ⊆ Ω` be a finite extension of the number field `k` with `[M : k] ≤ 2` (`hfr`), let
`f ∈ (𝓞 k)[X]` be monic of degree `2` whose reduction `g` modulo `Q` is irreducible, and let
`θ ∈ 𝓞 M` be a root of `f`.  Then for every prime `w` of `𝓞 M` lying over `Q`,

* `f(w|Q) ≥ deg g = 2`, because the reduction of `θ` modulo `w` is a root of the irreducible `g`,
  so that `deg g ≤ f(w|Q)` (`natDegree_le_inertiaDeg_of_aeval_eq_zero`);
* `e(w|Q) · f(w|Q) = [M_w : k_Q] ≤ [M : k] ≤ 2` (`finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg`
  and `finrank_adicCompletion_le_finrank`).

Hence `f(w|Q) = 2` and `e(w|Q) = 1`. -/
theorem ramificationIdx_eq_one_inertiaDeg_eq_two_of_quadratic_reduction (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (M : IntermediateField k Ω) [NumberField ↥M] [FiniteDimensional k ↥M]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (f : Polynomial (NumberField.RingOfIntegers k)) (hfmonic : f.Monic) (hfdeg : f.natDegree = 2)
    (g : Polynomial (NumberField.RingOfIntegers k ⧸ Q.asIdeal))
    (hgirr : Irreducible g) (hmap : Polynomial.map (Ideal.Quotient.mk Q.asIdeal) f = g)
    (θ : NumberField.RingOfIntegers ↥M) (hθ : Polynomial.aeval θ f = 0)
    (hfr : Module.finrank k ↥M ≤ 2) :
    ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
      w.asIdeal.LiesOver Q.asIdeal →
        w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
        w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 2 := by
  intro w hw
  classical
  haveI : w.asIdeal.LiesOver Q.asIdeal := hw
  haveI hmaxQ : Q.asIdeal.IsMaximal := Q.isMaximal
  haveI hmaxw : w.asIdeal.IsMaximal := w.isMaximal
  haveI hfinS : Finite (NumberField.RingOfIntegers ↥M ⧸ w.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum w
  -- `g` is monic of degree two
  have hgmonic : g.Monic := by rw [← hmap]; exact hfmonic.map _
  have hgcd : (Ideal.Quotient.mk Q.asIdeal) f.leadingCoeff ≠ 0 := by
    rw [hfmonic.leadingCoeff, map_one]; exact one_ne_zero
  have hgdeg : g.natDegree = 2 := by
    rw [← hmap, Polynomial.natDegree_map_of_leadingCoeff_ne_zero (Ideal.Quotient.mk Q.asIdeal) hgcd]
    exact hfdeg
  -- the inertia degree is at least the degree of `g`
  have hres : 2 ≤ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    have h := Commons.NumberTheory.NumberField.Completion.natDegree_le_inertiaDeg_of_aeval_eq_zero
      (R := NumberField.RingOfIntegers k) (S := NumberField.RingOfIntegers ↥M)
      Q.asIdeal w.asIdeal f g hgmonic hgirr hmap θ hθ
    omega
  -- `e · f` is the local degree, which is at most `[M : k]`
  letI : Algebra (Q.adicCompletion k) (w.adicCompletion ↥M) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q w hw)
  have hmul :=
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := k) (L := ↥M) Q w hw
  have hle :=
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
      (K := k) (L := ↥M) Q w hw
  have hepos : 0 < w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) :=
    Ideal.ramificationIdx_pos (NumberField.RingOfIntegers k) w.asIdeal
  have h1 : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
      w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) ≤ 2 := by
    rw [hmul]; exact hle.trans hfr
  have hf2 : w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 2 := by
    have h2 : w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) ≤
        w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
          w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
      Nat.le_mul_of_pos_left _ hepos
    omega
  refine ⟨?_, hf2⟩
  have hge : 2 ≤ w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
      w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    calc 2 ≤ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := hres
      _ ≤ w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
            w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
          Nat.le_mul_of_pos_left _ hepos
  have hprod : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
      w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 2 := le_antisymm h1 hge
  have h2 : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) * 2 = 2 := by
    have hh := hprod
    rw [hf2] at hh
    exact hh
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) (by rw [one_mul]; exact h2)

/-- **The integrality step.**  If `θ ∈ Ω` lies in the intermediate field `M` and is a root of a
*monic* polynomial `f ∈ (𝓞 k)[X]` (mapped into `Ω`), then `θ` is an algebraic integer of `M`: it is
the image of an element `θ'` of the ring of integers `𝓞 ↥M` which is a root of `f` over `𝓞 k`.

Indeed `θ` is integral over `𝓞 k` (root of the monic `f`), hence over `ℤ` (`ℤ ⊆ 𝓞 k ⊆ k` is a tower
of finite extensions), hence lies in `𝓞 ↥M = IsIntegralClosure ℤ ↥M`; the evaluation is compatible
with the algebra maps `𝓞 k → 𝓞 ↥M → ↥M`. -/
theorem exists_ringOfIntegers_aeval_eq_zero_root (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (M : IntermediateField k Ω) [FiniteDimensional k ↥M]
    (f : Polynomial (NumberField.RingOfIntegers k)) (hfmonic : f.Monic)
    (θ : Ω) (hmem : θ ∈ M)
    (hθ : (Polynomial.map (algebraMap (NumberField.RingOfIntegers k) Ω) f).IsRoot θ) :
    ∃ θ' : NumberField.RingOfIntegers ↥M,
      (θ' : ↥M) = ⟨θ, hmem⟩ ∧ Polynomial.aeval θ' f = 0 := by
  classical
  let R := NumberField.RingOfIntegers k
  -- ## `θ` is a root of `f` over `R`, hence integral over `R`
  have hθR : Polynomial.aeval θ f = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hθ
  have hintR : IsIntegral R θ := ⟨f, hfmonic, hθR⟩
  -- ## `θ` is integral over `ℤ`
  haveI hIR : Algebra.IsIntegral ℤ R := inferInstance
  have hintZ : IsIntegral ℤ θ := isIntegral_trans (R := ℤ) (A := R) θ hintR
  -- ## `θ`, viewed in `M`, is integral over `ℤ`
  have hintM : IsIntegral ℤ (⟨θ, hmem⟩ : ↥M) :=
    IsIntegral.tower_bot (R := ℤ) (A := ↥M) (B := Ω) (algebraMap ↥M Ω).injective (by
      rw [show (algebraMap ↥M Ω) ⟨θ, hmem⟩ = θ from rfl]
      exact hintZ)
  -- ## hence `θ` is an element of `𝓞 ↥M`
  obtain ⟨θ', hθ'map⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := NumberField.RingOfIntegers ↥M)
      (R := ℤ) (B := ↥M)).mp hintM
  refine ⟨θ', hθ'map, ?_⟩
  -- ## `f` vanishes at `θ'`
  have hA : Polynomial.aeval (⟨θ, hmem⟩ : ↥M) (f.map (algebraMap R k)) = 0 := by
    have h1 := Polynomial.map_aeval_eq_aeval_map (R := k) (S := ↥M) (T := Ω) (U := Ω)
      (φ := algebraMap k Ω) (ψ := algebraMap ↥M Ω) (by ext x; rfl)
      (f.map (algebraMap R k)) ⟨θ, hmem⟩
    have h2 : (algebraMap ↥M Ω)
        (Polynomial.aeval (⟨θ, hmem⟩ : ↥M) (f.map (algebraMap R k))) = 0 := by
      rw [h1]
      have h3 : (f.map (algebraMap R k)).map (algebraMap k Ω) =
          f.map (algebraMap R Ω) := by
        rw [Polynomial.map_map]; congr 1
      rw [h3]
      exact hθ
    exact (algebraMap ↥M Ω).injective (by rw [h2, map_zero])
  apply NumberField.RingOfIntegers.coe_injective (K := ↥M)
  rw [map_zero]
  have h5 := Polynomial.map_aeval_eq_aeval_map
    (R := R) (S := NumberField.RingOfIntegers ↥M) (T := ↥M) (U := ↥M)
    (φ := algebraMap R ↥M)
    (ψ := algebraMap (NumberField.RingOfIntegers ↥M) ↥M) (by ext x; rfl) f θ'
  rw [h5, hθ'map]
  have h6 : f.map (algebraMap R ↥M) =
      (f.map (algebraMap R k)).map (algebraMap k ↥M) := by
    rw [Polynomial.map_map]; congr 1
  rw [h6, ← Polynomial.aeval_eq_aeval_map (R := k) (S := ↥M) (T := ↥M)
    (φ := algebraMap k ↥M) (by ext x; rfl) (f.map (algebraMap R k)) ⟨θ, hmem⟩]
  exact hA

/-- **A quadratic level over `k` which is unramified at a prescribed finite place and in which that place is inert.**

`Q` is a finite place of the number field `k`, `Ω` is algebraically closed with `k → Ω`.  We produce a
level `M : IntermediateField k Ω` which is a number field, Galois and cyclic over `k` of degree `2`,
such that *every* prime `w` of `𝓞 M` above `Q` satisfies `e(w|Q) = 1` (unramified) and `f(w|Q) = 2`
(inert; equivalently the decomposition group of `w` in `Gal(M/k) ≅ ℤ/2` is everything).

Route (the naive "non-square residue class" does NOT work when the residue characteristic is `2`,
e.g. `k = ℚ`, `Q = (2)`, where `κ(Q) = 𝔽₂` has no non-square unit, yet `M = ℚ(√5)` is the desired
answer).  Instead we use the *unramified* extension of the local field `k_Q` directly, in the global
form given by `Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg`:
there is a monic `f ∈ (𝓞 k)[X]` of degree `2` whose reduction modulo `Q` is irreducible (a lift of an
irreducible quadratic over the finite field `κ(Q)`); a root `θ` of `f` in `Ω` then generates a
level `M = k⟮θ⟯` with `[M : k] ≤ 2`, and the reduction of `θ` modulo any prime above `Q` is a root
of the irreducible `g`, forcing `f(w|Q) ≥ 2` while `e(w|Q)·f(w|Q) = [M_w : k_Q] ≤ [M : k] ≤ 2`.
Hence `e(w|Q) = 1` and `f(w|Q) = 2` for *every* `w | Q`, and in particular `[M : k] = 2`, so that
`M/k` is Galois with cyclic Galois group of order `2`. -/
theorem cyclic_degree_two_unramified_inert_at_place (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :
    ∃ (M : IntermediateField k Ω) (_ : NumberField ↥M) (_ : FiniteDimensional k ↥M)
      (_ : IsGalois k ↥M),
      IsCyclic (↥M ≃ₐ[k] ↥M) ∧ Nat.card (↥M ≃ₐ[k] ↥M) = 2 ∧
      ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
        w.asIdeal.LiesOver Q.asIdeal →
          w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
          w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 2 := by
  classical
  let R := NumberField.RingOfIntegers k
  haveI hfinQ : Finite (R ⧸ Q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
  letI : Field (R ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  haveI : Fintype (R ⧸ Q.asIdeal) := Fintype.ofFinite _
  -- ## an irreducible quadratic `g` over the residue field, and a monic lift `f` to `𝓞 k`
  obtain ⟨g, hgmonic, hgirr, hgdeg⟩ :=
    Commons.FieldTheory.Polynomial.exists_monic_irreducible_of_natDegree
      (F := R ⧸ Q.asIdeal) 2 (by norm_num)
  obtain ⟨f, hfmonic, hfdeg, hfmap⟩ :=
    Commons.RingTheory.Polynomial.exists_monic_lift_of_surjective
      (Ideal.Quotient.mk Q.asIdeal) Ideal.Quotient.mk_surjective g hgmonic
  have hfndeg : f.natDegree = 2 := hfdeg.trans hgdeg
  let p : Polynomial k := f.map (algebraMap R k)
  have hpmonic : p.Monic := hfmonic.map _
  have hpdeg : p.natDegree = 2 := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero (algebraMap R k) (by
      rw [hfmonic.leadingCoeff, map_one]; exact one_ne_zero)]
    exact hfndeg
  let F : Polynomial Ω := f.map (algebraMap R Ω)
  have hFmonic : F.Monic := hfmonic.map _
  have hFdeg : F.natDegree = 2 := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero (algebraMap R Ω) (by
      rw [hfmonic.leadingCoeff, map_one]; exact one_ne_zero)]
    exact hfndeg
  have hFdegnz : F.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hFmonic.ne_zero, hFdeg]; norm_num
  -- ## a root `θ` of `f` in `Ω`, and the level `M = k⟮θ⟯`
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_root F hFdegnz
  let M : IntermediateField k Ω := k⟮θ⟯
  have hmem : θ ∈ M := IntermediateField.mem_adjoin_simple_self k θ
  have key : Polynomial.map (algebraMap k Ω) p = F := by
    show Polynomial.map (algebraMap k Ω) (Polynomial.map (algebraMap R k) f)
      = Polynomial.map (algebraMap R Ω) f
    rw [Polynomial.map_map]; congr 1
  have hroot : Polynomial.aeval θ p = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, key]
    exact hθ
  have hint : IsIntegral k θ := ⟨p, hpmonic, hroot⟩
  haveI hfd : FiniteDimensional k ↥M := IntermediateField.adjoin.finiteDimensional hint
  haveI hnf : NumberField ↥M := NumberField.of_module_finite k ↥M
  have hfinrank_le : Module.finrank k ↥M ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hint]
    calc (minpoly k θ).natDegree ≤ p.natDegree :=
          Polynomial.natDegree_le_of_dvd (minpoly.dvd k θ hroot) hpmonic.ne_zero
      _ = 2 := hpdeg
  haveI hgal : IsGalois k ↥M := isGalois_of_finrank_le_two hfinrank_le
  -- ## the local computation
  obtain ⟨θ', -, hθ'⟩ := exists_ringOfIntegers_aeval_eq_zero_root k Ω M f hfmonic θ hmem hθ
  have hchain := ramificationIdx_eq_one_inertiaDeg_eq_two_of_quadratic_reduction k Ω M Q f
    hfmonic hfndeg g hgirr hfmap θ' hθ' hfinrank_le
  -- ## `[M : k] = 2`
  obtain ⟨w₀, hw₀⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := k) (L := ↥M) Q
  have hA := hchain w₀ hw₀
  have hfinrank : Module.finrank k ↥M = 2 := by
    have hle := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
      (K := k) (L := ↥M) Q w₀ hw₀
    letI : Algebra (Q.adicCompletion k) (w₀.adicCompletion ↥M) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q w₀ hw₀)
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := k) (L := ↥M) Q w₀ hw₀, hA.1, one_mul, hA.2] at hle
    omega
  refine ⟨M, inferInstance, inferInstance, inferInstance, ?_, ?_, hchain⟩
  · refine isCyclic_of_prime_card (p := 2) ?_
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  · rw [IsGalois.card_aut_eq_finrank, hfinrank]

end Work.SSGRoute.Sha2Lib

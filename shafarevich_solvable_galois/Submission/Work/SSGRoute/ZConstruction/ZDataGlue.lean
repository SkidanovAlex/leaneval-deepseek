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
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `z`-data calculus of Schmidt--Wingberg Theorem 13

`Work.SSGRoute.shafarevich_z_construction` is proved from the existence of a cochain `z`
satisfying the six properties of Schmidt--Wingberg's Theorem 13 (§4): additivity and local
constancy on `G_K = K.fixingSubgroup`, agreement with `y` on the decomposition groups of the
places conjugate to `S`, vanishing on the involutions, vanishing on the inertia of the places
outside `cs(S)` that do not split in `Λ`, and the sharpened condition (b) at the places outside
`cs(S)` that *do* split in `Λ` (Schmidt--Wingberg's `z_P` cyclic and `z^σ_P = 0` for `σ ≠ 1`).

This file packages those six properties as the predicate `Work.SSGRoute.HasZData` and proves the
structural lemmas used by the induction of Schmidt--Wingberg (§4, pp. 18--19), which assembles the
answer for a general coefficient module `E` from answers for the components of a decomposition
`E = E₀ ⊕ μ_p`:

* `Work.SSGRoute.hasZData_add` -- the `z`-data is closed under addition.  The two hypotheses are
  exactly the two facts the paper verifies separately for the summands: **disjointness** of the
  ramification at a good place (so that at a place where the sum is ramified only one summand
  contributes, and its local group, being that of a one-dimensional coefficient module, is cyclic)
  and the **vanishing at the conjugates** of the good places.  This is the paper's "it is now easily
  verified that the class `z = z⁰ + inf z⁰⁰` satisfies conditions (a) and (b)";
* `Work.SSGRoute.kills_decomp_of_split_of_vanishes` -- the **level change**: a cochain vanishing on
  the Galois group `G_L` of an intermediate field `L ⊇ K` kills the local group of every place
  splitting completely in `L`.  In the paper this is the mechanism by which the primes of
  `T'(K) ∖ T(K)` receive no contribution from `z⁰` (they split completely in the Galois closure
  `K̃` of the field cut out by `z⁰`), which is the disjointness hypothesis above;
* `Work.SSGRoute.zadd_conj` -- **conjugation triviality**: for an additive cochain on `G_K` with
  abelian coefficients, conjugating by an element of `G_K` does not change values.  Consequently the
  sharpened condition (b) has to be checked at only one place per prime of `K` over a given prime
  of `k`: the conditions at the `G_K`-conjugate places are automatically equivalent.  (This is why
  the statement of (b) with "every conjugate `Q` that is not `G_K`-conjugate to `B`" is the paper's
  `z^σ_P = 0` for `σ ∈ G(K|k) ∖ {1}` and no more.)
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {E : Type} [AddCommGroup E]

section Basics

/-- For an additive cochain on `G_K`, the value at `1` is zero. -/
lemma zadd_one {K : IntermediateField k Ω} {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) :
    z 1 = 0 := by
  have h := hzadd 1 K.fixingSubgroup.one_mem 1 K.fixingSubgroup.one_mem
  rw [mul_one] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

/-- For an additive cochain on `G_K`, the value at an inverse is the negative. -/
lemma zadd_inv {K : IntermediateField k Ω} {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    {g : Ω ≃ₐ[k] Ω} (hg : g ∈ K.fixingSubgroup) : z g⁻¹ = -z g := by
  have h := hzadd g hg g⁻¹ (K.fixingSubgroup.inv_mem hg)
  rw [mul_inv_cancel] at h
  have h2 : z g + z g⁻¹ = 0 := by rw [← h, zadd_one hzadd]
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h2)

/-- **Conjugation triviality.**  For an additive cochain on `G_K` with abelian coefficients,
conjugation by an element of `G_K` does not change the values.  Hence the sharpened condition (b),
which requires the vanishing of `z` on the local group of *every* conjugate `Q` of a good place `B`
that is not `G_K`-conjugate to `B`, is a condition at one place per prime of `K` over a given prime
of `k`. -/
theorem zadd_conj {K : IntermediateField k Ω} {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    {τ u : Ω ≃ₐ[k] Ω} (hτ : τ ∈ K.fixingSubgroup) (hu : u ∈ K.fixingSubgroup) :
    z (τ * u * τ⁻¹) = z u := by
  have hτu : τ * u ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hτ hu
  have h1 : z (τ * u * τ⁻¹) = z (τ * u) + z τ⁻¹ :=
    hzadd (τ * u) hτu τ⁻¹ (K.fixingSubgroup.inv_mem hτ)
  rw [h1, hzadd τ hτ u hu, zadd_inv hzadd hτ]
  abel

/-- **Level change.**  A cochain vanishing on the Galois group of an intermediate field `L ⊇ K`
kills the local group (intersected with `G_K`) of every place that splits completely in `L`.  In
Schmidt--Wingberg's induction this is the reason why the field cut out by the class `z⁰` (whose
Galois group contains `G_{K̃}`, `K̃` the Galois closure of the cut-out field) contributes nothing at
the new primes of the second summand, which are chosen to split completely in `K̃`. -/
theorem kills_decomp_of_split_of_vanishes {K L : IntermediateField k Ω}
    {z : (Ω ≃ₐ[k] Ω) → E} (hz : ∀ g ∈ L.fixingSubgroup, z g = 0)
    {B : ValuationSubring Ω} (hsplit : SSGRoute.IsSplitIn k L B) :
    ∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z τ = 0 := by
  intro τ hτ
  exact hz τ (hsplit (Subgroup.mem_inf.mp hτ).1)

end Basics

/-! ## The `z`-data -/

/-- A finite place `B` of `Ω` is a **good place** for the pair `(Λ, S)`: it lies over a prime of `k`
outside the conjugates of `S` and splits completely in `Λ`.  These are exactly the places at which
the sharpened condition (b) of the `z`-data is triggered. -/
def IsGoodPlace (Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (B : ValuationSubring Ω) : Prop :=
  SSGRoute.IsFinPlace k B ∧ (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
    SSGRoute.IsSplitIn k Λ B

/-- **The `z`-data of Schmidt--Wingberg Theorem 13, relative to a cochain `y`.**  The six
properties that the auxiliary class `z` has to satisfy; only its values on
`K.fixingSubgroup` occur. -/
def HasZData (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (y z : (Ω ≃ₐ[k] Ω) → E) : Prop :=
  (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
  SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
    ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
  (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
    ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
    (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
    (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        z δ ∈ AddSubgroup.zmultiples (z g)) ∧
    (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0))

/-- **The `z`-data is closed under addition** (Schmidt--Wingberg §4, the final verification of the
induction on `dim_{𝔽_p} E`).

The hypotheses are exactly the two facts verified separately for the summands in the paper:

* **disjointness** at a good place: if the sum is ramified at `B`, then one of the summands vanishes
  identically on the local group of `B`; then the local group of the sum at `B` is the local group
  of the *other* summand, and the cyclicity clause for the sum follows from the cyclicity clause for
  that summand;
* **vanishing at the conjugates**: both summands kill the local group of every conjugate `Q` of `B`
  that is not `G_K`-conjugate to `B`. -/
theorem hasZData_add {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {y₀ y₁ z₀ z₁ : (Ω ≃ₐ[k] Ω) → E} (h₀ : HasZData K Λ S y₀ z₀) (h₁ : HasZData K Λ S y₁ z₁)
    (hdisj : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
        (z₀ σ ≠ 0 ∨ z₁ σ ≠ 0)) →
      ((∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z₀ τ = 0) ∨
       (∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z₁ τ = 0)))
    (hconj : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
        (z₀ σ ≠ 0 ∨ z₁ σ ≠ 0)) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z₀ τ = 0 ∧ z₁ τ = 0) :
    HasZData K Λ S (y₀ + y₁) (z₀ + z₁) := by
  obtain ⟨ha₀, hl₀, hg₀, hi₀, hs₀, hb₀⟩ := h₀
  obtain ⟨ha₁, hl₁, hg₁, hi₁, hs₁, hb₁⟩ := h₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    simp only [Pi.add_apply]
    rw [ha₀ g hg h hh, ha₁ g hg h hh]
    abel
  · obtain ⟨U₀, hU₀o, hU₀⟩ := hl₀
    obtain ⟨U₁, hU₁o, hU₁⟩ := hl₁
    refine ⟨U₀ ⊓ U₁, hU₀o.inter hU₁o, ?_⟩
    intro g hg u hu huH
    obtain ⟨hu₀, hu₁⟩ := Subgroup.mem_inf.mp hu
    simp only [Pi.add_apply]
    rw [hU₀ g hg u hu₀ huH, hU₁ g hg u hu₁ huH]
  · intro B hB hconjB σ hσK hσd
    simp only [Pi.add_apply]
    rw [hg₀ B hB hconjB σ hσK hσd, hg₁ B hB hconjB σ hσK hσd]
  · intro c hc hc2
    simp only [Pi.add_apply]
    rw [hi₀ c hc hc2, hi₁ c hc hc2, add_zero]
  · intro B hB hnot hsp σ hσK hσI
    simp only [Pi.add_apply]
    rw [hs₀ B hB hnot hsp σ hσK hσI, hs₁ B hB hnot hsp σ hσK hσI, add_zero]
  · intro B hB hnot hsp htrig
    obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
    have hzne : z₀ σ ≠ 0 ∨ z₁ σ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hσne (by simp only [Pi.add_apply]; rw [hc.1, hc.2, add_zero])
    have hgood : IsGoodPlace Λ S B := ⟨hB, hnot, hsp⟩
    have hram : ∃ s : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧
        (z₀ s ≠ 0 ∨ z₁ s ≠ 0) := ⟨σ, hσI, hσK, hzne⟩
    have hσmem : σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup :=
      Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩
    refine ⟨?_, ?_⟩
    · rcases hdisj B hgood hram with hz₀ | hz₁
      · -- the first summand is locally zero, so the second one carries the local group
        have hram₁ : ∃ s : Ω ≃ₐ[k] Ω,
            SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧ z₁ s ≠ 0 := by
          refine ⟨σ, hσI, hσK, ?_⟩
          rcases hzne with h | h
          · exact absurd (hz₀ σ hσmem) h
          · exact h
        obtain ⟨g, hg, hgc⟩ := (hb₁ B hB hnot hsp hram₁).1
        refine ⟨g, hg, fun δ hδ => ?_⟩
        have h1 : z₀ g = 0 := hz₀ g hg
        have h2 : z₀ δ = 0 := hz₀ δ hδ
        have h3 : z₁ δ ∈ AddSubgroup.zmultiples (z₁ g) := hgc δ hδ
        simp only [Pi.add_apply]
        simpa only [h1, h2, zero_add] using h3
      · have hram₀ : ∃ s : Ω ≃ₐ[k] Ω,
            SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧ z₀ s ≠ 0 := by
          refine ⟨σ, hσI, hσK, ?_⟩
          rcases hzne with h | h
          · exact h
          · exact absurd (hz₁ σ hσmem) h
        obtain ⟨g, hg, hgc⟩ := (hb₀ B hB hnot hsp hram₀).1
        refine ⟨g, hg, fun δ hδ => ?_⟩
        have h1 : z₁ g = 0 := hz₁ g hg
        have h2 : z₁ δ = 0 := hz₁ δ hδ
        have h3 : z₀ δ ∈ AddSubgroup.zmultiples (z₀ g) := hgc δ hδ
        simp only [Pi.add_apply]
        simpa only [h1, h2, add_zero] using h3
    · intro Q hQ hnconj τ hτ
      obtain ⟨hτ₀, hτ₁⟩ := hconj B hgood hram Q hQ hnconj τ hτ
      simp only [Pi.add_apply]
      rw [hτ₀, hτ₁, add_zero]

/-- **The induction step of Schmidt--Wingberg §4, with the two mechanisms made explicit.**

This replaces the two abstract hypotheses of `hasZData_add` by the two facts that the paper's §4
construction supplies for the two summands:

* `hz₀` -- the class `z₀` (the induction-hypothesis part, with a coefficient module of smaller
  dimension) **vanishes on the Galois group of a level `L'`**;
* `hconf` -- every good place at which `z₁` (the one-dimensional part) is **ramified splits
  completely, together with all its conjugates, in `L'`**.  Then the level change
  `kills_decomp_of_split_of_vanishes` shows that `z₀` kills the local group of the place and of all
  its conjugates, which is the disjointness needed at the new primes of `z₁`;
* `hkill` -- `z₁` **vanishes on the local groups of the conjugates** of every good place at which
  `z₀` is ramified (in the paper: the auxiliary class `ỹ` is prescribed to vanish at `T'(K) ∖ T(K)`,
  the places over the ramification of `z⁰`).

With these, `z₀ + z₁` satisfies the `z`-data for `y₀ + y₁`. -/
theorem hasZData_add_of_split_confined {K Λ L' : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {y₀ y₁ z₀ z₁ : (Ω ≃ₐ[k] Ω) → E}
    (h₀ : HasZData K Λ S y₀ z₀) (h₁ : HasZData K Λ S y₁ z₁)
    (hz₀ : ∀ g ∈ L'.fixingSubgroup, z₀ g = 0)
    (hconf : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z₁ σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q → SSGRoute.IsSplitIn k L' Q)
    (hkill : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z₀ σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z₁ τ = 0) :
    HasZData K Λ S (y₀ + y₁) (z₀ + z₁) := by
  obtain ⟨ha₀, hl₀, hg₀, hi₀, hs₀, hb₀⟩ := h₀
  obtain ⟨ha₁, hl₁, hg₁, hi₁, hs₁, hb₁⟩ := h₁
  have hlev : ∀ B : ValuationSubring Ω, SSGRoute.IsSplitIn k L' B →
      ∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z₀ τ = 0 :=
    fun B hB => kills_decomp_of_split_of_vanishes hz₀ hB
  refine hasZData_add ⟨ha₀, hl₀, hg₀, hi₀, hs₀, hb₀⟩ ⟨ha₁, hl₁, hg₁, hi₁, hs₁, hb₁⟩ ?_ ?_
  · -- disjointness of the ramification at a good place
    intro B hgood hram
    obtain ⟨σ, hσI, hσK, hzne⟩ := hram
    by_cases hram₁ : ∃ s : Ω ≃ₐ[k] Ω,
        SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧ z₁ s ≠ 0
    · exact Or.inl (hlev B (hconf B hgood hram₁ B (isConjPlace_refl B)))
    · have hz₁ : ∀ s : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B s → s ∈ K.fixingSubgroup →
          z₁ s = 0 := fun s hIs hm => by
        by_contra hne
        exact hram₁ ⟨s, hIs, hm, hne⟩
      refine Or.inr (hkill B hgood ?_ B (isConjPlace_refl B))
      rcases hzne with h | h
      · exact ⟨σ, hσI, hσK, h⟩
      · exact absurd (hz₁ σ hσI hσK) h
  · -- vanishing on the conjugates that are not `G_K`-conjugates
    intro B hgood hram Q hQ hnconj τ hτ
    obtain ⟨σ, hσI, hσK, hzne⟩ := hram
    by_cases hram₁ : ∃ s : Ω ≃ₐ[k] Ω,
        SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧ z₁ s ≠ 0
    · -- `z₀` dies at `Q` by the level change, since `Q` is a conjugate of `B`
      refine ⟨hlev Q (hconf B hgood hram₁ Q hQ) τ hτ,
        (hb₁ B hgood.1 hgood.2.1 hgood.2.2 hram₁).2 Q hQ hnconj τ hτ⟩
    · have hz₁ : ∀ s : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B s → s ∈ K.fixingSubgroup →
          z₁ s = 0 := fun s hIs hm => by
        by_contra hne
        exact hram₁ ⟨s, hIs, hm, hne⟩
      have hram₀ : ∃ s : Ω ≃ₐ[k] Ω,
          SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧ z₀ s ≠ 0 := by
        rcases hzne with h | h
        · exact ⟨σ, hσI, hσK, h⟩
        · exact absurd (hz₁ σ hσI hσK) h
      exact ⟨(hb₀ B hgood.1 hgood.2.1 hgood.2.2 hram₀).2 Q hQ hnconj τ hτ,
        hkill B hgood hram₀ Q hQ τ hτ⟩

/-- **Change of coefficients along an injective additive map.**  All six clauses of the `z`-data are
equalities between values of the two cochains or vanishings of one of them, so they are preserved
(and reflected) by an injective additive map.  This is how the induction of Schmidt--Wingberg passes
from the submodule `ker π` of `E` back to `E`, and how the stated `z`-data for a subquotient is
transported to the ambient module. -/
theorem hasZData_map {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) {K Λ : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → A} {z : (Ω ≃ₐ[k] Ω) → A}
    (h : HasZData K Λ S y z) :
    HasZData K Λ S (fun σ => f (y σ)) (fun σ => f (z σ)) := by
  obtain ⟨ha, hl, hg, hi, hs, hb⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg' h hh'
    show f (z (g * h)) = f (z g) + f (z h)
    rw [ha g hg' h hh', map_add]
  · obtain ⟨U, hUo, hU⟩ := hl
    refine ⟨U, hUo, ?_⟩
    intro g hg' u hu huK
    show f (z (g * u)) = f (z g)
    rw [hU g hg' u hu huK]
  · intro B hB hc σ hσK hσd
    show f (z σ) = f (y σ)
    rw [hg B hB hc σ hσK hσd]
  · intro c hc hc2
    show f (z c) = 0
    rw [hi c hc hc2, map_zero]
  · intro B hB hn hs' σ hσK hσI
    show f (z σ) = 0
    rw [hs B hB hn hs' σ hσK hσI, map_zero]
  · intro B hB hn hs' htrig
    have htrig' : ∃ σ : Ω ≃ₐ[k] Ω,
        SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0 := by
      obtain ⟨σ, hI, hK, hne⟩ := htrig
      exact ⟨σ, hI, hK, fun h0 => hne (by show f (z σ) = 0; rw [h0, map_zero])⟩
    obtain ⟨hcyc, hvan⟩ := hb B hB hn hs' htrig'
    refine ⟨?_, ?_⟩
    · obtain ⟨g, hg', hgc⟩ := hcyc
      refine ⟨g, hg', fun δ hδ => ?_⟩
      show f (z δ) ∈ AddSubgroup.zmultiples (f (z g))
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgc δ hδ)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, by rw [← hm, map_zsmul]⟩
    · intro Q hQ hn' τ hτ
      show f (z τ) = 0
      rw [hvan Q hQ hn' τ hτ, map_zero]

/-- The `z`-data only depends on the cochain `y` through its pointwise values (only the agreement
clause mentions `y`).  This lets one replace `y₀ + y₁` by the given cochain `y` at the end of the
induction step. -/
theorem hasZData_congr {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {y y' z : (Ω ≃ₐ[k] Ω) → E} (h : ∀ σ, y' σ = y σ) (hz : HasZData K Λ S y' z) :
    HasZData K Λ S y z := by
  obtain ⟨ha, hl, hg, hi, hs, hb⟩ := hz
  refine ⟨ha, hl, ?_, hi, hs, hb⟩
  intro B hB hc σ hσK hσd
  rw [← h σ]
  exact hg B hB hc σ hσK hσd

/-- **The induction step with the coefficient module decomposed componentwise.**

This is the shape in which the induction on `dim_{𝔽_p} E` of Schmidt--Wingberg §4 is assembled.
Given a decomposition `y = y₀ + y₁` of the given cochain (in the paper: `E = E₀ ⊕ μ_p`, `y₀` the
`E₀`-component obtained from the induction hypothesis, `y₁ = π ∘ y` the one-dimensional part), a
`z`-data witness `z₀` for `y₀` (the induction hypothesis), a level `L'` on whose Galois group `z₀`
vanishes (the Galois closure of the field cut out by `z₀`), and a `z`-data witness `z₁` for `y₁`
whose ramification at good places is confined to places split completely in `L'` and which kills the
local groups of the conjugates of the good places where `z₀` is ramified (the auxiliary class `ỹ`),
the sum `z₀ + z₁` satisfies the `z`-data for `y`. -/
theorem hasZData_of_component_data {K Λ L' : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {y y₀ y₁ z₀ z₁ : (Ω ≃ₐ[k] Ω) → E}
    (hy : ∀ σ, y₀ σ + y₁ σ = y σ)
    (h₀ : HasZData K Λ S y₀ z₀) (h₁ : HasZData K Λ S y₁ z₁)
    (hz₀ : ∀ g ∈ L'.fixingSubgroup, z₀ g = 0)
    (hconf : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z₁ σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q → SSGRoute.IsSplitIn k L' Q)
    (hkill : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z₀ σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z₁ τ = 0) :
    HasZData K Λ S y (z₀ + z₁) :=
  hasZData_congr (fun σ => by rw [Pi.add_apply, hy σ])
    (hasZData_add_of_split_confined h₀ h₁ hz₀ hconf hkill)

end Work.SSGRoute

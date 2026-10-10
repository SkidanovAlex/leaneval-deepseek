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
import Submission.Work.SSGRoute.LTDDefs.toClass_apply_congr
import Submission.Work.SSGRoute.ZConstruction.finite_lcHoms_levelK_localGroup
import Submission.Work.SSGRoute.ZConstruction.localKummerHom
import Submission.Work.SSGRoute.finite_H1loc_inertia_free
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The class map of the level-`K` local Kummer character

The level-`K` local Kummer map sends a global unit `β ∈ Kˣ` to the class in
`H1loc p k Ω K (ZMod p) (decomp k A ⊓ K.fixingSubgroup)` of the locally constant `1`-cocycle

  `σ ↦ χ_β(σ)`  (`σ ∈ D_A ⊓ G_K`),

where `χ_β` is the Kummer character of `β` at the finite place `A` (`kummerCharHom`, i.e. the
element of `↥(lcHoms p ↥(decomp ↥K A))` classified by the local Kummer dictionary).  Because the
coefficient module is trivial on `G_K`, the coboundaries at `H = decomp k A ⊓ K.fixingSubgroup` are
exactly the functions vanishing on `H` (`isCoboundaryOn_iff_forall_eq_zero`), so the class of a
cocycle is determined by its restriction to `H` (`toClass_eq_iff_forall_eq`).

The resulting map `Ψ : Kˣ → H1loc …` is

* additive (`Ψ (β β') = Ψ β + Ψ β'`),
* with kernel exactly the local `p`-th powers (`NK.UchidaKummer.localPowClass ↥K p 𝔭 β = 1`),
* and hits the class of every locally constant cocycle on `G_K` (via the surjectivity of the
  Kummer character map `β ↦ χ_β` on `↥(lcHoms p ↥(decomp ↥K A))`).
-/

namespace Work.SSGRoute.ZDataMup

open Classical
open scoped Pointwise

section Helpers

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {H : Subgroup (Ω ≃ₐ[k] Ω)}
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- On a subgroup of `G_K = K.fixingSubgroup` the restriction `res k K` is trivial. -/
lemma res_eq_one_of_le_fixingSubgroup (hH : H ≤ K.fixingSubgroup)
    {g : Ω ≃ₐ[k] Ω} (hg : g ∈ H) : SSGRoute.res k K g = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (E := K)]
  exact hH hg

/-- On a subgroup of `G_K`, the `1`-coboundaries are exactly the functions vanishing on `H`. -/
lemma isCoboundaryOn_iff_forall_eq_zero (hH : H ≤ K.fixingSubgroup)
    (f : (Ω ≃ₐ[k] Ω) → ZMod p) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H f ↔ ∀ g ∈ H, f g = 0 := by
  constructor
  · rintro ⟨m, hm⟩ g hg
    rw [hm g hg, res_eq_one_of_le_fixingSubgroup hH hg, one_smul, sub_self]
  · intro h
    exact ⟨0, fun g hg => by rw [h g hg, smul_zero, sub_zero]⟩

/-- The class of a locally constant cocycle on `H ≤ G_K` is zero iff the cocycle vanishes on
`H`. -/
lemma toClass_eq_zero_iff_forall_eq_zero (hH : H ≤ K.fixingSubgroup)
    {f : (Ω ≃ₐ[k] Ω) → ZMod p} (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H) :
    Work.SSGRoute.toClass p k Ω K (ZMod p) H f = 0 ↔ ∀ g ∈ H, f g = 0 := by
  rw [Work.SSGRoute.toClass_eq_zero_iff p k Ω K (ZMod p) H hf,
    Work.SSGRoute.mem_coboundaries, isCoboundaryOn_iff_forall_eq_zero hH]

/-- Two locally constant cocycles on `H ≤ G_K` have the same class iff they agree on `H`. -/
lemma toClass_eq_iff_forall_eq (hH : H ≤ K.fixingSubgroup)
    {f f' : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H)
    (hf' : f' ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H) :
    Work.SSGRoute.toClass p k Ω K (ZMod p) H f =
        Work.SSGRoute.toClass p k Ω K (ZMod p) H f' ↔
      ∀ g ∈ H, f g = f' g := by
  constructor
  · intro h g hg
    exact Work.SSGRoute.LTDDefs.toClass_apply_congr p k Ω K H hH hf hf' h g hg
  · intro h
    have hcob : f - f' ∈ Work.SSGRoute.coboundaries p k Ω K (ZMod p) H := by
      rw [Work.SSGRoute.mem_coboundaries]
      refine (isCoboundaryOn_iff_forall_eq_zero hH _).mpr fun g hg => ?_
      show f g - f' g = 0
      rw [h g hg, sub_self]
    have hsub : f - f' ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H :=
      Submodule.sub_mem _ hf hf'
    rw [Work.SSGRoute.toClass, dif_pos hf, Work.SSGRoute.toClass, dif_pos hf',
      Submodule.mkQ_apply, Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [Submodule.mem_comap]
    have hsub' : (⟨f, hf⟩ - ⟨f', hf'⟩ : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H)) =
        ⟨f - f', hsub⟩ := Subtype.ext rfl
    rw [hsub']
    exact hcob

/-- Local constancy transfers from `IsLocConstOn` on a subgroup to the subgroup itself. -/
lemma isLocallyConstant_restrict_of_isLocConstOn {H : Subgroup (Ω ≃ₐ[k] Ω)}
    {f : (Ω ≃ₐ[k] Ω) → ZMod p} (hf : SSGRoute.IsLocConstOn H f) :
    _root_.IsLocallyConstant (fun h : ↥H => f (h : Ω ≃ₐ[k] Ω)) := by
  obtain ⟨U, hUo, hU⟩ := hf
  rw [_root_.IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y : ↥H => (x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) ⁻¹' (U : Set (Ω ≃ₐ[k] Ω)),
    hUo.preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
  · show (x : Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω) ∈ U
    rw [inv_mul_cancel]
    exact U.one_mem
  · intro y hy
    show f (y : Ω ≃ₐ[k] Ω) = f (x : Ω ≃ₐ[k] Ω)
    have hyH : (x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω) ∈ H :=
      H.mul_mem (H.inv_mem x.2) y.2
    have hthis := hU (x : Ω ≃ₐ[k] Ω) x.2 ((x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) hy hyH
    have hxy : (x : Ω ≃ₐ[k] Ω) * ((x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) =
        (y : Ω ≃ₐ[k] Ω) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [← hxy, hthis]

end Helpers

section ProperSubring

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- A prime-adic valuation subring is a proper subring: `A.comap` along the structure map of a
completion is never all of the field. -/
lemma valuationSubringAtPrime_ne_top (𝔭 : IsDedekindDomain.HeightOneSpectrum R) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 ≠ ⊤ := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
  infer_instance

end ProperSubring

section Extend

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- The additive character of `H = decomp k A ⊓ K.fixingSubgroup` attached to a locally constant
character of the level-`K` local group `↥(decomp ↥K A)`. -/
noncomputable def lcHomsToH (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ZMod p :=
  fun g => (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g)).toAdd

lemma lcHomsToH_apply (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)))
    (g : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    lcHomsToH A χ g = (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g)).toAdd := rfl

/-- The additive character attached to a locally constant character is a locally constant additive
`1`-cocycle on `H` (for the action through `res k K`, trivial on `H`). -/
lemma lcHomsToH_mem_Z1 (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    lcHomsToH A χ ∈
      Work.AbsoluteKummer.Z1 ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p) := by
  rw [Work.AbsoluteKummer.mem_Z1_iff]
  constructor
  · intro g h
    show (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A (g * h))).toAdd =
      g • (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd +
        (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g)).toAdd
    rw [map_mul (Work.SSGRoute.decompEquiv_fok k Ω K A), map_mul, toAdd_mul]
    have h2 : g • (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd =
        (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd := by
      rw [hcompat g, res_eq_one_of_le_fixingSubgroup (H := _) inf_le_right g.2, one_smul]
    rw [h2]
    abel
  · intro x
    have hχloc : _root_.IsLocallyConstant
        (χ.1 : ↥(SSGRoute.decomp (k := ↥K) A) → Multiplicative (ZMod p)) := χ.2
    obtain ⟨V, hVo, hxV, hV⟩ := hχloc.exists_open (Work.SSGRoute.decompEquiv_fok k Ω K A x)
    exact ⟨(Work.SSGRoute.decompEquiv_fok k Ω K A) ⁻¹' V,
      hVo.preimage (Work.SSGRoute.isHomeomorph_decompEquiv_fok k Ω K A).continuous,
      hxV, fun y hy => by
        show (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A y)).toAdd =
          (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A x)).toAdd
        rw [hV (Work.SSGRoute.decompEquiv_fok k Ω K A y) hy]⟩

/-- Extension by `0` off `H` of the additive character `lcHomsToH A χ`. -/
noncomputable def lcHomsExtend (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    (Ω ≃ₐ[k] Ω) → ZMod p :=
  (extendCocycle p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) hcompat
    ⟨lcHomsToH A χ, lcHomsToH_mem_Z1 A hcompat χ⟩).1

lemma lcHomsExtend_apply (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)))
    (g : Ω ≃ₐ[k] Ω) :
    lcHomsExtend A hcompat χ g =
      if hg : g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup then
        (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩)).toAdd else 0 := rfl

/-- The value of the extension on `H`. -/
lemma lcHomsExtend_apply_of_mem (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)))
    {g : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup) :
    lcHomsExtend A hcompat χ g =
      (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩)).toAdd := by
  rw [lcHomsExtend_apply, dif_pos hg]

/-- The extension is a locally constant `1`-cocycle on `H`. -/
lemma lcHomsExtend_mem (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    lcHomsExtend A hcompat χ ∈
      Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
  (extendCocycle p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) hcompat
    ⟨lcHomsToH A χ, lcHomsToH_mem_Z1 A hcompat χ⟩).2

/-- The extension is additive in the character. -/
lemma lcHomsExtend_add_apply (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ χ' : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)))
    (g : Ω ≃ₐ[k] Ω) :
    lcHomsExtend A hcompat (χ * χ') g =
      lcHomsExtend A hcompat χ g + lcHomsExtend A hcompat χ' g := by
  rw [lcHomsExtend_apply, lcHomsExtend_apply, lcHomsExtend_apply]
  by_cases hg : g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup
  · rw [dif_pos hg, dif_pos hg, dif_pos hg]
    have h1 : (χ * χ').1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩) =
        χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩) *
          χ'.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩) := by
      rw [Subgroup.coe_mul, MonoidHom.mul_apply]
    rw [h1, toAdd_mul]
  · rw [dif_neg hg, dif_neg hg, dif_neg hg, add_zero]

/-- The extension vanishes on `H` iff the character is trivial. -/
lemma lcHomsExtend_eq_zero_iff (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    (∀ g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, lcHomsExtend A hcompat χ g = 0) ↔ χ = 1 := by
  constructor
  · intro h
    refine Subtype.ext (MonoidHom.ext fun y => ?_)
    have h1 : lcHomsExtend A hcompat χ
        ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm y) = 0 := h _ ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm y).2
    rw [lcHomsExtend_apply, dif_pos ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm y).2] at h1
    have h2 : (Work.SSGRoute.decompEquiv_fok k Ω K A)
        ⟨(Work.SSGRoute.decompEquiv_fok k Ω K A).symm y,
          ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm y).2⟩ = y :=
      MulEquiv.apply_symm_apply _ y
    rw [h2] at h1
    show χ.1 y = (1 : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))).1 y
    have h3 : χ.1 y = Multiplicative.ofAdd (0 : ZMod p) := by
      calc χ.1 y = Multiplicative.ofAdd (χ.1 y).toAdd := (ofAdd_toAdd _).symm
        _ = Multiplicative.ofAdd 0 := by rw [h1]
    simpa using h3
  · intro h g hg
    rw [lcHomsExtend_apply, dif_pos hg]
    have h1 : χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩) = 1 := by rw [h]; rfl
    rw [h1]
    rfl

/-- The level-`K` local group at a place `A` of `Ω`. -/
abbrev kLevelLocalGroup (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (A : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  SSGRoute.decomp k A ⊓ K.fixingSubgroup

end Extend

section ExtendAdditivity

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- The extension is additive in the character (function form). -/
lemma lcHomsExtend_add (A : ValuationSubring Ω)
    [DistribMulAction ↥(kLevelLocalGroup k Ω K A) (ZMod p)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hcompat : ∀ (h : ↥(kLevelLocalGroup k Ω K A)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ χ' : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    lcHomsExtend A hcompat (χ * χ') =
      lcHomsExtend A hcompat χ + lcHomsExtend A hcompat χ' :=
  funext fun g => lcHomsExtend_add_apply A hcompat χ χ' g

end ExtendAdditivity

section Target

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- **Surjectivity of the Kummer character map** (the level-`K` local Kummer isomorphism in
character form): every locally constant character of the level-`K` local group is the Kummer
character of a global unit. -/
theorem kummerCharMonoidHom_surjective_aux [IsAlgClosed Ω] [NumberField ↥K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    Function.Surjective
      (Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA) := by
  classical
  haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- `A` is a finite place of `Ω` over `↥K` as well
  have hAK : SSGRoute.IsFinPlace ↥K A := by
    show A.comap (algebraMap ↥K Ω) ≠ ⊤
    rw [h𝔭]
    intro h
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
      (K := ↥K)] at h
    exact (Valuation.valuationSubring_eq_top_iff _).mp h inferInstance
  -- the prime of `K` below `A` is `𝔭`
  have hprime : 𝔭 = Submission.NeukirchUchida.primeOf A hAK := by
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers ↥K) (K := ↥K) ?_
    rw [← h𝔭]
    exact Submission.NeukirchUchida.primeOf_spec A hAK
  -- the descent `Kˣ ⧸ ker ρ →* lcHoms` is injective ...
  have hinj := Work.SSGRoute.ZConstruction.kummerCharLift_injective (p := p) (k := k) (Ω := Ω)
    (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭
  -- ... between finite groups of the same cardinality
  haveI hfinκ : Finite (((𝔭.adicCompletion ↥K)ˣ ⧸
      (powMonoidHom p : (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range)) :=
    Work.SSGRoute.finite_powClass_localField _ p Fact.out
  haveI hfinD : Finite (Kˣ ⧸ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) :=
    Finite.of_equiv (((𝔭.adicCompletion ↥K)ˣ ⧸
        (powMonoidHom p : (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range))
      (Work.SSGRoute.ZConstruction.quotientKerLocalPowClassEquiv (p := p) (K := K) 𝔭).symm.toEquiv
  haveI hfinL : Finite ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
    Work.SSGRoute.ZConstruction.finite_lcHoms_levelK_localGroup (p := p) (k := k) (Ω := Ω)
      (K := K) (A := A) hA hAK hAK
  haveI hFintypeD : Fintype (Kˣ ⧸ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) :=
    Fintype.ofFinite _
  haveI hFintypeL : Fintype ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
    Fintype.ofFinite _
  have hcard : Nat.card (Kˣ ⧸ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) =
      Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) := by
    rw [Nat.card_congr (Work.SSGRoute.ZConstruction.quotientKerLocalPowClassEquiv
      (p := p) (K := K) 𝔭).toEquiv,
      Work.SSGRoute.ZConstruction.natCard_lcHoms_levelK_localGroup (p := p) (k := k)
        (Ω := Ω) (K := K) A hA hAK hAK, hprime]
  have hsurj : Function.Bijective (Work.SSGRoute.ZConstruction.kummerCharLift (p := p) (k := k)
      (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭) :=
    (Fintype.bijective_iff_injective_and_card
      (Work.SSGRoute.ZConstruction.kummerCharLift (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭)).mpr
      ⟨hinj, by simpa only [Nat.card_eq_fintype_card] using hcard⟩
  -- consequently the Kummer character map `β ↦ χ_β` is surjective
  intro χ
  obtain ⟨q, hq⟩ := hsurj.2 χ
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective
    (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) q
  refine ⟨β, ?_⟩
  rw [← Work.SSGRoute.ZConstruction.kummerCharLift_mk (p := p) (k := k) (Ω := Ω) (K := K)
    (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭 β]
  exact hq

/-- **The character of a cocycle on `G_K`**: restricting a locally constant `1`-cocycle on
`K.fixingSubgroup` to `H = decomp k A ⊓ K.fixingSubgroup` and transporting along
`decompEquiv_fok` gives a locally constant character of the level-`K` local group. -/
theorem exists_lcHoms_of_cocycle_aux
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → ZMod p)
    (ha : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) K.fixingSubgroup) :
    ∃ χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)),
      ∀ g : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g) = Multiplicative.ofAdd (a g) := by
  classical
  have hHle : SSGRoute.decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
  -- on `H` the action is trivial, so the cocycle condition is additivity
  have hcyc : SSGRoute.IsCocycleOn (SSGRoute.res k K)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a :=
    fun g hg h hh => ha.1 g (hHle hg) h (hHle hh)
  have hlocOn : SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a :=
    let ⟨U, hUo, hU⟩ := ha.2
    ⟨U, hUo, fun g hg u hu huH => hU g (hHle hg) u hu (hHle huH)⟩
  have hadd : ∀ g h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      a ((g * h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) : Ω ≃ₐ[k] Ω) =
        a (g : Ω ≃ₐ[k] Ω) + a (h : Ω ≃ₐ[k] Ω) := by
    intro g h
    have h1 := hcyc (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2
    rw [res_eq_one_of_le_fixingSubgroup hHle g.2, one_smul] at h1
    exact h1
  have hone : a (1 : Ω ≃ₐ[k] Ω) = 0 := by
    have h1 : a (1 : Ω ≃ₐ[k] Ω) = a (1 : Ω ≃ₐ[k] Ω) + a (1 : Ω ≃ₐ[k] Ω) := by
      have h := hadd 1 1
      simpa using h
    have h2 : a (1 : Ω ≃ₐ[k] Ω) + a (1 : Ω ≃ₐ[k] Ω) = a (1 : Ω ≃ₐ[k] Ω) + 0 := by
      rw [add_zero]
      exact h1.symm
    exact add_left_cancel h2
  have hloc0 : _root_.IsLocallyConstant
      (fun g : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) => a (g : Ω ≃ₐ[k] Ω)) :=
    isLocallyConstant_restrict_of_isLocConstOn hlocOn
  -- the character of `↥H` defined by `a`
  let ψ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →* Multiplicative (ZMod p) :=
    { toFun := fun g => Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω))
      map_one' := by
        show Multiplicative.ofAdd (a (1 : Ω ≃ₐ[k] Ω)) = 1
        rw [hone]
        rfl
      map_mul' := by
        intro g h
        show Multiplicative.ofAdd (a ((g * h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
            Ω ≃ₐ[k] Ω)) =
          Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω)) *
            Multiplicative.ofAdd (a (h : Ω ≃ₐ[k] Ω))
        rw [hadd, ofAdd_add] }
  have hψloc : _root_.IsLocallyConstant ψ := hloc0.comp Multiplicative.ofAdd
  -- transport along `decompEquiv_fok : H ≃* decomp ↥K A`
  have hsymm : Continuous ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm :
      ↥(SSGRoute.decomp (k := ↥K) A) → ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :=
    (Work.SSGRoute.decompEquiv_fok k Ω K A).toEquiv.continuous_symm_iff.2
      (Work.SSGRoute.isHomeomorph_decompEquiv_fok k Ω K A).isOpenMap
  refine ⟨⟨ψ.comp (Work.SSGRoute.decompEquiv_fok k Ω K A).symm.toMonoidHom, ?_⟩, ?_⟩
  · exact hψloc.comp_continuous hsymm
  · intro g
    show ψ ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm
      (Work.SSGRoute.decompEquiv_fok k Ω K A g)) = Multiplicative.ofAdd (a g)
    rw [MulEquiv.symm_apply_apply]
    rfl

end Target

theorem LT_levelK_kummerClassMap
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    ∃ Ψ : Kˣ → Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      (∀ β β' : Kˣ, Ψ (β * β') = Ψ β + Ψ β') ∧
      (∀ β : Kˣ, Ψ β = 0 ↔ NK.UchidaKummer.localPowClass ↥K p 𝔭 β = 1) ∧
      (∀ (a : (Ω ≃ₐ[k] Ω) → ZMod p),
        a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) K.fixingSubgroup →
        ∃ β : Kˣ, Ψ β = Work.SSGRoute.toClass p k Ω K (ZMod p)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a) := by
  classical
  haveI hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  -- the action of the level-`K` local group on the coefficients, through `res`
  letI : DistribMulAction ↥(kLevelLocalGroup k Ω K A) (ZMod p) :=
    Work.SSGRoute.subgroupDistribMulAction k Ω K (ZMod p) (kLevelLocalGroup k Ω K A)
  have hcompat : ∀ (h : ↥(kLevelLocalGroup k Ω K A)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m := fun _ _ => rfl
  have hle : kLevelLocalGroup k Ω K A ≤ K.fixingSubgroup := inf_le_right
  -- a primitive `p`-th root of unity in `↥K`
  have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (ζ := ⟨ζ, hζK⟩)
      (by simpa using hζ) (algebraMap ↥K Ω).injective
  refine ⟨fun β => Work.SSGRoute.toClass p k Ω K (ZMod p) (kLevelLocalGroup k Ω K A)
      (lcHomsExtend A hcompat (Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p)
        (k := k) (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA β)), ?_, ?_, ?_⟩
  · intro β β'
    have hfun : lcHomsExtend A hcompat (Work.SSGRoute.ZConstruction.kummerCharMonoidHom
          (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA
          (β * β')) =
        lcHomsExtend A hcompat (Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p)
          (k := k) (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA β) +
        lcHomsExtend A hcompat (Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p)
          (k := k) (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA β') := by
      rw [map_mul, lcHomsExtend_add]
    simp only [hfun]
    refine Work.SSGRoute.toClass_add p k Ω K (ZMod p) (kLevelLocalGroup k Ω K A) ?_ ?_
    · exact lcHomsExtend_mem A hcompat _
    · exact lcHomsExtend_mem A hcompat _
  · intro β
    have hmem : lcHomsExtend A hcompat (Work.SSGRoute.ZConstruction.kummerCharMonoidHom
        (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA β) ∈
        Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (kLevelLocalGroup k Ω K A) :=
      lcHomsExtend_mem A hcompat _
    rw [toClass_eq_zero_iff_forall_eq_zero hle hmem]
    rw [lcHomsExtend_eq_zero_iff A hcompat]
    exact Work.SSGRoute.ZConstruction.kummerCharMonoidHom_eq_one_iff (p := p) (k := k)
      (Ω := Ω) (K := K) (ζ := ⟨ζ, hζK⟩) (hζ := hζK') (A := A) hA 𝔭 h𝔭 β
  · intro a ha
    have haH : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) (kLevelLocalGroup k Ω K A) :=
      ⟨fun g hg h hh => ha.1 g (hle hg) h (hle hh),
        (let ⟨U, hUo, hU⟩ := ha.2
         ⟨U, hUo, fun g hg u hu huH => hU g (hle hg) u hu (hle huH)⟩)⟩
    obtain ⟨χ, hχ⟩ := exists_lcHoms_of_cocycle_aux (p := p) (k := k) (Ω := Ω) (K := K) A hA a ha
    obtain ⟨β, hβ⟩ := kummerCharMonoidHom_surjective_aux (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ⟨ζ, hζK⟩) (hζ := hζK') A hA 𝔭 h𝔭 χ
    refine ⟨β, ?_⟩
    refine (toClass_eq_iff_forall_eq hle (lcHomsExtend_mem A hcompat _) haH).mpr ?_
    intro g hg
    rw [lcHomsExtend_apply_of_mem A hcompat _ hg, hβ]
    rw [hχ ⟨g, hg⟩]
    rfl

end Work.SSGRoute.ZDataMup

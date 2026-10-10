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
import Submission.Work.SSGRoute.H1Pair.horth
import Submission.Work.SSGRoute.coker_aux
import Submission.Work.SSGRoute.h1_finite_stage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open CategoryTheory

namespace Work.SSGRoute

/-! ## Elementary pushforwards of the local predicates -/

section Pushforward

variable {Γ G M N : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
  [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N]

/-- The local constancy predicate pushes forward along any function. -/
theorem IsLocConstOn.comp {H : Subgroup Γ} {f : Γ → M} (hf : SSGRoute.IsLocConstOn H f)
    (φ : M → N) : SSGRoute.IsLocConstOn H (fun x => φ (f x)) := by
  obtain ⟨U, hU, h⟩ := hf
  exact ⟨U, hU, fun g hg u hu huH => by
    show φ (f (g * u)) = φ (f g)
    rw [h g hg u hu huH]⟩

/-- The cocycle condition pushes forward along an additive, equivariant map. -/
theorem IsCocycleOn.comp (act : Γ →* G) {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCocycleOn act H f) (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    SSGRoute.IsCocycleOn act H (fun x => φ (f x)) := by
  intro g hg h hh
  show φ (f (g * h)) = φ (f g) + act g • φ (f h)
  rw [hf g hg h hh, map_add, hφ]

/-- The coboundary condition pushes forward along an additive, equivariant map. -/
theorem IsCoboundaryOn.comp (act : Γ →* G) {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCoboundaryOn act H f) (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    SSGRoute.IsCoboundaryOn act H (fun x => φ (f x)) := by
  obtain ⟨m, hm⟩ := hf
  exact ⟨φ m, fun g hg => by
    show φ (f g) = act g • φ m - φ m
    rw [hm g hg, map_sub, hφ]⟩

end Pushforward

/-! ## Finiteness of the Tate twist of a finite module by a line -/

/-- A one-dimensional `𝔽_p`-module is finite as a type. -/
theorem finite_of_finrank_eq_one (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) : Finite T := by
  haveI : Module.Free (ZMod p) T := inferInstance
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by omega)
  have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
    rw [h, Module.finrank_self]
  exact Finite.of_injective (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p)
    (LinearEquiv.injective _)

/-- `E ⊗ T` is a finite type when `E` is finite and `T` is a line. -/
theorem finite_tensor_of_finrank_eq_one (p : ℕ) [Fact p.Prime] (E T : Type) [AddCommGroup E]
    [Module (ZMod p) E] [Finite E] [AddCommGroup T] [Module (ZMod p) T]
    (h : Module.finrank (ZMod p) T = 1) : Finite (E ⊗[ZMod p] T) := by
  haveI : Module.Free (ZMod p) T := inferInstance
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by omega)
  have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
    rw [h, Module.finrank_self]
  have e : E ⊗[ZMod p] T ≃ₗ[ZMod p] E ⊗[ZMod p] (ZMod p) :=
    TensorProduct.congr (LinearEquiv.refl (ZMod p) E)
      (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p)
  have e₂ : E ⊗[ZMod p] (ZMod p) ≃ₗ[ZMod p] E := TensorProduct.rid (ZMod p) E
  exact Finite.of_injective ((e.trans e₂ : E ⊗[ZMod p] T ≃ₗ[ZMod p] E) : E ⊗[ZMod p] T → E)
    (LinearEquiv.injective _)

/-! ## A functional separating a point from a submodule (over `𝔽_p`) -/

/-- Over a field, a vector outside a submodule is separated from it by a linear functional:
there is `φ` vanishing on `S` with `φ x ≠ 0`. -/
theorem exists_dual_eq_zero_on_of_notMem (p : ℕ) [Fact p.Prime] {A : Type} [AddCommGroup A]
    [Module (ZMod p) A] (S : Submodule (ZMod p) A) {x : A} (hx : x ∉ S) :
    ∃ φ : A →ₗ[ZMod p] ZMod p, (∀ y ∈ S, φ y = 0) ∧ φ x ≠ 0 := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ S.zero_mem)
  have hxq : (Submodule.Quotient.mk (p := S) x : A ⧸ S) ≠ 0 := fun h =>
    hx ((Submodule.Quotient.mk_eq_zero S).mp h)
  set L : Submodule (ZMod p) (A ⧸ S) := Submodule.span (ZMod p)
    ({Submodule.Quotient.mk (p := S) x} : Set (A ⧸ S)) with hL
  have hxL : Submodule.Quotient.mk (p := S) x ∈ L := Submodule.subset_span (by simp)
  let ψ : ZMod p →ₗ[ZMod p] L :=
    (LinearMap.toSpanSingleton (ZMod p) (A ⧸ S) (Submodule.Quotient.mk (p := S) x)).codRestrict L
      (fun c => by
        have h : c • (Submodule.Quotient.mk (p := S) x) ∈ L := Submodule.smul_mem _ c hxL
        simpa using h)
  have hψapply : ∀ c : ZMod p, ((ψ c : L) : A ⧸ S) = c • Submodule.Quotient.mk (p := S) x := by
    intro c
    rfl
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro a b hab
      have h : a • (Submodule.Quotient.mk (p := S) x) = b • (Submodule.Quotient.mk (p := S) x) := by
        rw [← hψapply a, ← hψapply b, hab]
      have h1 : (a - b) • (Submodule.Quotient.mk (p := S) x) = 0 := by
        rw [sub_smul]
        exact sub_eq_zero.mpr h
      rcases (smul_eq_zero.mp h1) with h2 | h2
      · exact sub_eq_zero.mp h2
      · exact absurd h2 hxq
    · intro y
      have hy : (y : A ⧸ S) ∈ Submodule.span (ZMod p)
          ({Submodule.Quotient.mk (p := S) x} : Set (A ⧸ S)) := y.2
      rw [Submodule.mem_span_singleton] at hy
      obtain ⟨c, hc⟩ := hy
      refine ⟨c, Subtype.ext ?_⟩
      rw [hψapply]
      exact hc
  obtain ⟨Φ, hΦ⟩ := LinearMap.exists_extend (p := L)
    (f := (LinearEquiv.ofBijective ψ hψbij).symm.toLinearMap)
  refine ⟨Φ.comp (Submodule.mkQ S), ?_, ?_⟩
  · intro y hy
    show Φ (Submodule.mkQ S y) = 0
    have h0 : Submodule.mkQ S y = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hy
    rw [h0, map_zero]
  · have hψ1 : ψ (1 : ZMod p) = (⟨Submodule.Quotient.mk (p := S) x, hxL⟩ : L) := by
      apply Subtype.ext
      rw [hψapply, one_smul]
    have h2 : (LinearEquiv.ofBijective ψ hψbij).symm
        (⟨Submodule.Quotient.mk (p := S) x, hxL⟩ : L) = 1 := by
      rw [← hψ1]
      exact (LinearEquiv.ofBijective ψ hψbij).symm_apply_apply 1
    have h1 : Submodule.mkQ S x = (⟨Submodule.Quotient.mk (p := S) x, hxL⟩ : L) := by
      rw [Submodule.mkQ_apply]
    show Φ (Submodule.mkQ S x) ≠ 0
    rw [h1]
    have hΦy : Φ ((⟨Submodule.Quotient.mk (p := S) x, hxL⟩ : L) : A ⧸ S)
        = (LinearEquiv.ofBijective ψ hψbij).symm ⟨Submodule.Quotient.mk (p := S) x, hxL⟩ := by
      have h := congrArg (fun (g : L →ₗ[ZMod p] ZMod p) => g ⟨Submodule.Quotient.mk (p := S) x, hxL⟩) hΦ
      simpa [LinearMap.comp_apply] using h
    rw [hΦy, h2]
    exact one_ne_zero

end Work.SSGRoute



namespace Work.SSGRoute

/-! ## Step 5: factoring the coefficient map through the finite stage -/

section StageFactorization

variable {p : ℕ} {K : Type} [Group K]

/-- **The factorization of an equivariant pushforward through a finite stage.**

Let `i : W →ₗ E₂` be an injective `K`-equivariant map of `𝔽_p[K]`-modules, `f : E →ₗ E₂` a
`K`-equivariant map and `T` a nontrivial `K`-module.  If the `𝔽_p`-linear map
`F₀ : E ⊗ T →ₗ W ⊗ T` satisfies `(i ⊗ id_T) ∘ F₀ = f ⊗ id_T` on pure tensors, then `f` factors
through `i` by a `K`-equivariant `f₀ : E →ₗ W`, and `F₀ = f₀ ⊗ id_T`.

`[Nontrivial T]` is needed: for `T = 0` the tensor hypothesis is vacuous while the conclusion can
fail.  The proof separates `f e` from `range i` with a functional `λ` killing `i` (using a nonzero
`t : T` and `smul_eq_zero` over the field `𝔽_p`). -/
theorem exists_f0_of_rTensor_eq (p : ℕ) [Fact p.Prime] (K : Type) [Group K]
    (E W E₂ T : Type)
    [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction K E] [SMulCommClass K (ZMod p) E]
    [AddCommGroup W] [Module (ZMod p) W] [DistribMulAction K W] [SMulCommClass K (ZMod p) W]
    [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction K E₂] [SMulCommClass K (ZMod p) E₂]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction K T] [SMulCommClass K (ZMod p) T]
    [Nontrivial T]
    (i : W →ₗ[ZMod p] E₂) (hi : Function.Injective i)
    (hiK : ∀ (g : K) (w : W), i (g • w) = g • i w)
    (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K) (e : E), f (g • e) = g • f e)
    (F₀ : TensorProduct (ZMod p) E T →ₗ[ZMod p] TensorProduct (ZMod p) W T)
    (hF₀ : ∀ (e : E) (t : T), (LinearMap.rTensor T i) (F₀ (e ⊗ₜ[ZMod p] t))
        = f e ⊗ₜ[ZMod p] t) :
    ∃ f₀ : E →ₗ[ZMod p] W,
      (∀ (g : K) (e : E), f₀ (g • e) = g • f₀ e) ∧
      (∀ e : E, i (f₀ e) = f e) ∧
      (∀ (e : E) (t : T), F₀ (e ⊗ₜ[ZMod p] t) = f₀ e ⊗ₜ[ZMod p] t) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hinj : Function.Injective ((LinearMap.rTensor T) i) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := T) i hi
  have hcoe : ∀ y : LinearMap.range i,
      i ((LinearEquiv.ofInjective i hi).symm y) = (y : E₂) :=
    fun y => LinearEquiv.ofInjective_symm_apply i y
  have hmem : ∀ e : E, f e ∈ LinearMap.range i := by
    intro e
    by_contra hmem
    obtain ⟨lam, hlam0, hlamx⟩ :=
      exists_dual_eq_zero_on_of_notMem p (LinearMap.range i) hmem
    have hcomp : (lam ∘ₗ i) = 0 := LinearMap.ext (fun y => hlam0 (i y) ⟨y, rfl⟩)
    obtain ⟨t₀, ht₀⟩ := exists_ne (0 : T)
    have hzero : (lam (f e)) ⊗ₜ[ZMod p] t₀ = 0 := by
      have h1 : ((LinearMap.rTensor T) lam)
          (((LinearMap.rTensor T) i) (F₀ (e ⊗ₜ[ZMod p] t₀))) = 0 := by
        rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp, LinearMap.rTensor_zero,
          LinearMap.zero_apply]
      rw [hF₀ e t₀, LinearMap.rTensor_tmul] at h1
      exact h1
    rw [← (TensorProduct.lid (ZMod p) T).injective.eq_iff, map_zero,
      TensorProduct.lid_tmul] at hzero
    rcases (smul_eq_zero.mp hzero) with h' | h'
    · exact hlamx h'
    · exact ht₀ h'
  let f₀ : E →ₗ[ZMod p] W :=
    (LinearEquiv.ofInjective i hi).symm.toLinearMap ∘ₗ
      (f.codRestrict (LinearMap.range i) hmem)
  have hf₀ : ∀ e : E, i (f₀ e) = f e := by
    intro e
    show i ((LinearEquiv.ofInjective i hi).symm
        ((f.codRestrict (LinearMap.range i) hmem) e)) = f e
    rw [hcoe, LinearMap.codRestrict_apply]
  have hf₀K : ∀ (g : K) (e : E), f₀ (g • e) = g • f₀ e := by
    intro g e
    apply hi
    rw [hf₀, hiK, hf₀, hf]
  have hF₀' : ∀ (e : E) (t : T), F₀ (e ⊗ₜ[ZMod p] t) = f₀ e ⊗ₜ[ZMod p] t := by
    intro e t
    apply hinj
    rw [hF₀ e t]
    simp only [LinearMap.rTensor_tmul, hf₀]
  exact ⟨f₀, hf₀K, hf₀, hF₀'⟩

end StageFactorization

/-! ## The finite stage as a module over the smaller group -/

/-- **The finite stage, with the coefficient module seen as a module over the smaller group.**

Variant of `Work.SSGRoute.h1_finite_stage` in which the ambient coefficient module `E₂` carries a
`K`-module structure and the `G₂`-module structure used by the finite-stage construction is the
pullback of it along `π₂ : G₂ →* K`.  The output `E₂₀` is a finite `K`-module, `i` is `K`-equivariant
and the `G₂`-action on `E₂₀` is (definitionally) the pullback of the `K`-action, so that
`F₀ : M₁ ⟶ Rep.res φ (Rep.res π₂ (of (K, E₂₀ ⊗ T)))` literally has the required type.

The proof repeats the construction of `h1_finite_stage` with the actions on the finite stage `↥W`
defined as the restrictions of those on `E₂`; `hπ₂` (surjectivity of `π₂`) makes the `G₂`-stable
submodule `W` also `K`-stable. -/
theorem exists_finite_stage_K (p : ℕ) [Fact p.Prime]
    {G₁ G₂ : Type} [Group G₁] [Group G₂] [Fintype G₂]
    (K : Type) [Group K] (π₂ : G₂ →* K) (hπ₂ : Function.Surjective π₂)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
      [DistribMulAction K T] [SMulCommClass K (ZMod p) T]
    (M₁ : Rep (ZMod p) G₁) [Finite M₁.V]
    (φ : G₁ →* G₂)
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
      [DistribMulAction K E₂] [SMulCommClass K (ZMod p) E₂]
    (F : M₁ ⟶ Rep.res φ (Rep.res π₂ (Rep.of
      (Representation.ofDistribMulAction (ZMod p) K (TensorProduct (ZMod p) E₂ T)))))
    (x : groupHomology.H1 M₁)
    (hx : (ModuleCat.Hom.hom (groupHomology.map φ F 1)) x = 0) :
    ∃ (E₂₀ : Type) (_ : AddCommGroup E₂₀) (_ : Module (ZMod p) E₂₀)
      (_ : DistribMulAction K E₂₀) (_ : SMulCommClass K (ZMod p) E₂₀) (_ : Finite E₂₀)
      (i : E₂₀ →ₗ[ZMod p] E₂) (_ : Function.Injective i)
      (_ : ∀ (g : K) (m : E₂₀), i (g • m) = g • i m)
      (F₀ : M₁ ⟶ Rep.res φ (Rep.res π₂ (Rep.of
        (Representation.ofDistribMulAction (ZMod p) K (TensorProduct (ZMod p) E₂₀ T))))),
      (∀ z : M₁.V, F.hom z = (LinearMap.rTensor T i) (F₀.hom z)) ∧
      (ModuleCat.Hom.hom (groupHomology.map φ F₀ 1)) x = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI hGE₂ : DistribMulAction G₂ E₂ := DistribMulAction.compHom E₂ π₂
  letI hGT : DistribMulAction G₂ T := DistribMulAction.compHom T π₂
  letI hSCE₂ : SMulCommClass G₂ (ZMod p) E₂ := ⟨fun g c e => by
    show (π₂ g) • (c • e) = c • ((π₂ g) • e)
    rw [smul_comm]⟩
  letI hSCT : SMulCommClass G₂ (ZMod p) T := ⟨fun g c t => by
    show (π₂ g) • (c • t) = c • ((π₂ g) • t)
    rw [smul_comm]⟩
  haveI : Fintype M₁.V := Fintype.ofFinite M₁.V
  revert hx
  refine groupHomology.H1_induction_on x ?_
  intro z hz
  have hY : ((groupHomology.mapCycles₁ φ F z).1 : G₂ →₀ TensorProduct (ZMod p) E₂ T)
      ∈ groupHomology.boundaries₁ (Rep.res π₂ (Rep.of (Representation.ofDistribMulAction
          (ZMod p) K (TensorProduct (ZMod p) E₂ T)))) := by
    rw [← groupHomology.H1π_eq_zero_iff]
    rw [← groupHomology.H1π_comp_map_apply φ F z]
    exact hz
  obtain ⟨B, hB⟩ := LinearMap.mem_range.mp hY
  let ι : Type := M₁.V ⊕ G₂ ⊕ (G₂ × G₂)
  haveI : Fintype ι := inferInstanceAs (Fintype (M₁.V ⊕ G₂ ⊕ (G₂ × G₂)))
  let mm : ι → TensorProduct (ZMod p) E₂ T := fun i => match i with
    | Sum.inl v => F.hom v
    | Sum.inr (Sum.inl g) =>
        ((groupHomology.mapCycles₁ φ F z).1 : G₂ →₀ TensorProduct (ZMod p) E₂ T) g
    | Sum.inr (Sum.inr q) => B q
  obtain ⟨W, -, hWstab, hWfin, m', hm'⟩ :=
    exists_finite_stable_submodule_family p G₂ E₂ T (∅ : Set E₂) Set.finite_empty mm
  -- `W` is also `K`-stable, because `G₂` acts through the surjection `π₂`
  have hKstab : ∀ (g : K) (w : E₂), w ∈ W → g • w ∈ W := by
    intro g w hw
    obtain ⟨γ, rfl⟩ := hπ₂ g
    exact hWstab γ w hw
  letI hDMK : DistribMulAction K ↥W :=
    { smul := fun (g : K) (x : ↥W) => ⟨g • (x : E₂), hKstab g x x.2⟩
      one_smul := fun x => Subtype.ext (one_smul K (x : E₂))
      mul_smul := fun g h x => Subtype.ext (mul_smul g h (x : E₂))
      smul_zero := fun g => Subtype.ext (smul_zero g)
      smul_add := fun g x y => Subtype.ext (smul_add g (x : E₂) (y : E₂)) }
  letI hsmK : SMul K ↥W :=
    @SMulZeroClass.toSMul K ↥W _
      (@DistribSMul.toSMulZeroClass K ↥W _
        (@DistribMulAction.toDistribSMul K ↥W _ _ hDMK))
  letI hsmZ : SMul (ZMod p) ↥W :=
    @SMulZeroClass.toSMul (ZMod p) ↥W _
      (@DistribSMul.toSMulZeroClass (ZMod p) ↥W _
        (@DistribMulAction.toDistribSMul (ZMod p) ↥W _ _
          (@Module.toDistribMulAction (ZMod p) ↥W _ _ (inferInstance : Module (ZMod p) ↥W))))
  letI hSCK : SMulCommClass K (ZMod p) ↥W :=
    @Function.Injective.smulCommClass K (ZMod p) ↥W E₂ hsmK hsmZ _ _ _
      (Subtype.val : ↥W → E₂) Subtype.val_injective
      (fun g x => rfl) (fun c x => rfl)
  letI hDMG : DistribMulAction G₂ ↥W := DistribMulAction.compHom ↥W π₂
  letI hsmG : SMul G₂ ↥W :=
    @SMulZeroClass.toSMul G₂ ↥W _
      (@DistribSMul.toSMulZeroClass G₂ ↥W _
        (@DistribMulAction.toDistribSMul G₂ ↥W _ _ hDMG))
  letI hSCG : SMulCommClass G₂ (ZMod p) ↥W :=
    @Function.Injective.smulCommClass G₂ (ZMod p) ↥W E₂ hsmG hsmZ _ _ _
      (Subtype.val : ↥W → E₂) Subtype.val_injective
      (fun g x => rfl) (fun c x => rfl)
  have hFrange : ∀ v : M₁.V, F.hom v ∈ LinearMap.range (W.subtype.rTensor T) := by
    intro v
    refine ⟨m' (Sum.inl v), ?_⟩
    have h := hm' (Sum.inl v)
    simpa [mm, LinearMap.rTensor_def] using h
  have hBrange : ∀ q : G₂ × G₂, B q ∈ LinearMap.range (W.subtype.rTensor T) := by
    intro q
    refine ⟨m' (Sum.inr (Sum.inr q)), ?_⟩
    have h := hm' (Sum.inr (Sum.inr q))
    simpa [mm, LinearMap.rTensor_def] using h
  obtain ⟨F₀, hF₀1, hF₀2⟩ :=
    exists_finite_stage_factor (p := p) (φ := φ) (T := T) (M₁ := M₁) (E₂ := E₂) (E₂₀ := ↥W)
      (i := W.subtype) (hi := fun a b h => Subtype.ext h)
      (hiG := fun g m => rfl) (F := F) (z := z) (B := B)
      (hB := hB) (hB0 := hBrange) (hF0 := hFrange)
  exact ⟨↥W, inferInstance, inferInstance, hDMK, hSCK, hWfin, W.subtype,
    (fun a b h => Subtype.ext h), (fun g m => rfl), F₀, hF₀1, hF₀2⟩

end Work.SSGRoute

/-! ## The assembly -/

section Assembly

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (πN : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (hπN : ∀ σ : Ω ≃ₐ[k] Ω, πN (SSGRoute.res k N σ) = SSGRoute.res k K σ)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → E)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))

/-- Shorthand for the coefficient module of the assembly. -/
noncomputable abbrev cokerM₁ : Rep (ZMod p) (N ≃ₐ[k] N) :=
  Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T)))

end Assembly

namespace Work.SSGRoute

/-- **The assembly of `coker_obstruction`.**  All of the formal content of the theorem, given the
two arithmetic inputs: a family of local pairings with clauses (1),(2),(3),(5) (`pair`, `hadd₁`,
`hadd₂`, `hcob`, `hnat`) and the realizability statement `hreal` of Poitou--Tate at `H¹` (SW
Lemma 10, relaxed at `cs(N)`). -/
theorem coker_obstruction_of_inputs (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (πN : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (hπN : ∀ σ : Ω ≃ₐ[k] Ω, πN (SSGRoute.res k N σ) = SSGRoute.res k K σ)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → E)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))
    (pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
          ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p)
    (hloc : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (H : Subgroup (Ω ≃ₐ[k] Ω)),
        Work.SSGRoute.H1Pair.IsLocalGroup k Ω H →
          Work.SSGRoute.H1Pair.PairClauses p K T M (fun a b => pair M H a b) H)
    (hnat : ∀ (M M₂ : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
        (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
        (f' : Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p]
          Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
        (hff' : ∀ (φ : Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
        (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        pair M₂ H (fun σ => f (a σ)) b = pair M H a (fun σ => f' (b σ)))
    (hreal : ∀ (N₂ : IntermediateField k Ω) [FiniteDimensional k N₂] [IsGalois k N₂]
        (hKN₂ : K ≤ N₂)
        (hSram₂ : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (SSGRoute.IsRamifiedIn k N₂ B ∨ B.valuation (p : Ω) < 1) →
          ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
        (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (α' : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M) (β' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
        (hα' : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α' A) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α' A))
        (hβ' : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β' c))
        (horth : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N₂ B →
            SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) →
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N₂ B →
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0) →
          ∑ A ∈ S, pair M (SSGRoute.decomp k A) (α' A) b +
            ∑ c ∈ C, pair M (Subgroup.zpowers c) (β' c) b = 0),
        ∃ ε : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
          (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun σ => ε σ - α' A σ)) ∧
          (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
            (fun σ => ε σ - β' c σ)) ∧
          ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N₂ B →
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0) :
    ∃ x : groupHomology.H1 (Rep.res πN
        (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T)))),
      ∀ (N₂ : IntermediateField k Ω) [FiniteDimensional k N₂] [IsGalois k N₂],
        K ≤ N₂ → N₂ ≤ N →
        ∀ (q : (N ≃ₐ[k] N) →* (N₂ ≃ₐ[k] N₂)),
        (∀ σ : Ω ≃ₐ[k] Ω, q (SSGRoute.res k N σ) = SSGRoute.res k N₂ σ) →
        ∀ (π₂ : (N₂ ≃ₐ[k] N₂) →* (K ≃ₐ[k] K)),
        (∀ σ : Ω ≃ₐ[k] Ω, π₂ (SSGRoute.res k N₂ σ) = SSGRoute.res k K σ) →
        ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
          (f : E →ₗ[ZMod p] E₂), (∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e) →
        ∀ (F : Rep.res πN
              (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T))) ⟶
            Rep.res q (Rep.res π₂
              (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E₂ ⊗[ZMod p] T))))),
        (∀ z : E ⊗[ZMod p] T, F.hom z = f.rTensor T z) →
        (groupHomology.map q F 1).hom x = 0 →
        ∃ ε : (Ω ≃ₐ[k] Ω) → E₂,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
          (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun σ => ε σ - f (α A σ))) ∧
          (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
            (fun σ => ε σ - f (β c σ))) ∧
          ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N₂ B →
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hfinET : Finite (E ⊗[ZMod p] T) :=
    finite_tensor_of_finrank_eq_one p E T hT.1
  -- ## Step 1: the obstruction functional `ω` on the level-`N` cocycles
  obtain ⟨Φ, hΦcob, hΦform⟩ :=
    Work.SSGRoute.H1Pair.omega_functional_contra p k Ω K N hKN ζ hζ hζK E T hT πN hπN
      (pair E) (hloc E) S hSfin C hCinv α hα β hβ
  -- ## Step 2: the class `x` of `H₁` which is Tate-dual to `ω`
  obtain ⟨x, hx⟩ :=
    Work.SSGRoute.H1Pair.exists_x_of_Phi p
      (Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T))))
      Φ hΦcob
  refine ⟨x, ?_⟩
  intro N₂ _ _ hKN₂ hN₂N q hq π₂ hπ₂ E₂ _ _ _ _ f hf F hF hmap
  -- ## Step 3: the finite stage of the coefficient module, as a `Gal(K/k)`-module
  -- (`π₂` is surjective because it intertwines `π₂` with the surjections `res k ·`)
  have hπ₂surj : Function.Surjective π₂ := by
    intro g
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (E := Ω) (K₁ := ↥K) g
    exact ⟨SSGRoute.res k N₂ σ, by rw [hπ₂ σ]; exact hσ⟩
  obtain ⟨W, _, _, _, _, _, i, hi, hiK, F₀, hF₀F, hF₀x⟩ :=
    Work.SSGRoute.exists_finite_stage_K (p := p) (K := K ≃ₐ[k] K) (π₂ := π₂) (hπ₂ := hπ₂surj)
      (φ := q) (T := T)
      (M₁ := Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
        (E ⊗[ZMod p] T)))) (E₂ := E₂) F x hmap
  -- ## Step 4: the factorization of `f` through the finite stage
  haveI hNT : Nontrivial T :=
    Module.nontrivial_of_finrank_pos (R := ZMod p) (by rw [hT.1]; norm_num)
  have hF₀lin : ∀ z : E ⊗[ZMod p] T, F.hom z = (LinearMap.rTensor T i) (F₀.hom.toLinearMap z) :=
    fun z => hF₀F z
  obtain ⟨f₀, hf₀K, hf₀i, hf₀F⟩ :=
    Work.SSGRoute.exists_f0_of_rTensor_eq (p := p) (K := K ≃ₐ[k] K) (E := E) (W := W) (E₂ := E₂)
      (T := T) i hi hiK f hf F₀.hom.toLinearMap (fun e t => by
        rw [← hF₀lin (e ⊗ₜ[ZMod p] t), hF (e ⊗ₜ[ZMod p] t), LinearMap.rTensor_tmul])
  -- ## Step 5: the level-`N₂` vanishing of the functional (`H1Pair.transfer_sum_eq_zero`)
  have hΦ' : ∀ b : ↥(groupCohomology.cocycles₁ (Work.SSGRoute.H1Pair.contra (Rep.res πN (Rep.of
        (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T)))))),
      Φ b =
        S.sum (fun A => pair E (SSGRoute.decomp k A) (α A)
          (fun σ => (b : (N ≃ₐ[k] N) → Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))
            (SSGRoute.res k N σ))) +
        C.sum (fun c => pair E (Subgroup.zpowers c) (β c)
          (fun σ => (b : (N ≃ₐ[k] N) → Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))
            (SSGRoute.res k N σ))) :=
    fun b => hΦform b.1 b.2
  have htrans := Work.SSGRoute.H1Pair.transfer_sum_eq_zero (p := p) (k := k) (Ω := Ω)
    (K := K) (N := N) (N₂ := N₂) (E := E) (T := T) (πN := πN) (hπN := hπN) (q := q) (hq := hq)
    (π₂ := π₂) (hπ₂ := hπ₂) (M₂ := W) (f₀ := f₀) (hf₀ := hf₀K) (pair := pair) (hnat := hnat)
    (S := S) (hSfin := hSfin) (C := C) (hCinv := hCinv) (α := α) (hα := hα) (β := β) (hβ := hβ)
    (X := x) (Φ := Φ) (hΦ := hΦ') (hX := hx) (F₀ := F₀) (hF₀tmul := hf₀F) (hF₀zero := hF₀x)
  -- ## Step 6: the orthogonality hypothesis of Poitou--Tate (`H1Pair.horth_of_level_vanishing`)
  have horth := Work.SSGRoute.H1Pair.horth_of_level_vanishing (p := p) (k := k) (Ω := Ω)
    (K := K) (N₂ := N₂) (hKN₂ := hKN₂) (M₂ := W) (π₂ := π₂) (hπ₂ := hπ₂) (T := T) (E := E)
    (f₀ := f₀) (hf₀ := hf₀K) (pair := pair) (S := S) (hSfin := hSfin) (C := C) (hCinv := hCinv)
    (α := α) (β := β) (htransfer := htrans)
  -- ## Step 7: the Poitou--Tate input at the level `N₂` with the finite stage `W`
  have hSram₂ : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N₂ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B := by
    intro B hB h
    exact hSram B hB (h.imp (fun hr => Work.SSGRoute.isRamifiedIn_of_le hN₂N hr) id)
  have hα' : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun σ => f₀ (α A σ)) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (fun σ => f₀ (α A σ)) := by
    intro A hA
    exact ⟨Work.SSGRoute.IsCocycleOn.comp (SSGRoute.res k K) (hα A hA).1 f₀.toAddMonoidHom
        (fun g m => hf₀K g m),
      Work.SSGRoute.IsLocConstOn.comp (hα A hA).2 (fun m => f₀ m)⟩
  have hβ' : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (fun σ => f₀ (β c σ)) := by
    intro c hc
    exact Work.SSGRoute.IsCocycleOn.comp (SSGRoute.res k K) (hβ c hc) f₀.toAddMonoidHom
      (fun g m => hf₀K g m)
  obtain ⟨ε₀, hε₀coc, hε₀lc, hε₀cobS, hε₀cobC, hε₀iner⟩ :=
    hreal N₂ hKN₂ hSram₂ W (fun A σ => f₀ (α A σ)) (fun c σ => f₀ (β c σ)) hα' hβ' horth
  -- ## Step 8: push the global solution forward along the stage inclusion
  refine ⟨fun σ => i (ε₀ σ), ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.SSGRoute.IsCocycleOn.comp (SSGRoute.res k K) hε₀coc i.toAddMonoidHom
      (fun g m => hiK g m)
  · exact Work.SSGRoute.IsLocConstOn.comp hε₀lc (fun m => i m)
  · intro A hA
    have h := Work.SSGRoute.IsCoboundaryOn.comp (SSGRoute.res k K) (hε₀cobS A hA)
      i.toAddMonoidHom (fun g m => hiK g m)
    have hfe : (fun σ : Ω ≃ₐ[k] Ω => i (ε₀ σ) - f (α A σ))
        = fun σ => i (ε₀ σ - f₀ (α A σ)) := by
      funext σ
      rw [map_sub, hf₀i]
    rw [hfe]
    exact h
  · intro c hc
    have h := Work.SSGRoute.IsCoboundaryOn.comp (SSGRoute.res k K) (hε₀cobC c hc)
      i.toAddMonoidHom (fun g m => hiK g m)
    have hfe : (fun σ : Ω ≃ₐ[k] Ω => i (ε₀ σ) - f (β c σ))
        = fun σ => i (ε₀ σ - f₀ (β c σ)) := by
      funext σ
      rw [map_sub, hf₀i]
    rw [hfe]
    exact h
  · intro B hB hconj hsplit σ hσ
    show i (ε₀ σ) = 0
    rw [hε₀iner B hB hconj hsplit σ hσ, map_zero]

end Work.SSGRoute

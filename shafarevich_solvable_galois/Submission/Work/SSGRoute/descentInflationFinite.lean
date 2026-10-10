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
import Submission.Work.SSGRoute.H2locAux.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open scoped Pointwise

/-! ## The twisted `1`-coboundary and its calculus -/

section Basic

variable {G : Type} [Group G] {M : Type} [AddCommGroup M] [DistribMulAction G M]

/-- The twisted `1`-coboundary `(δβ)(g,h) = g • β h - β (g*h) + β g`. -/
def dlt (β : G → M) (g h : G) : M := g • β h - β (g * h) + β g

lemma dlt_add (β γ : G → M) (g h : G) :
    dlt (β + γ) g h = dlt β g h + dlt γ g h := by
  simp only [dlt, Pi.add_apply, smul_add]; abel

lemma dlt_cocycle (β : G → M) : SSGRoute.IsCocycle2 (MonoidHom.id G) (dlt β) := by
  intro g h l
  simp only [dlt, MonoidHom.id_apply, smul_sub, smul_add, mul_smul]
  rw [mul_assoc]; abel

lemma coc_sub {c c' : G → G → M}
    (hc : SSGRoute.IsCocycle2 (MonoidHom.id G) c) (hc' : SSGRoute.IsCocycle2 (MonoidHom.id G) c') :
    SSGRoute.IsCocycle2 (MonoidHom.id G) (fun g h => c g h - c' g h) := by
  intro g h l
  have h1 := hc g h l
  have h2 := hc' g h l
  simp only [MonoidHom.id_apply] at h1 h2 ⊢
  have key : g • (c h l - c' h l) - (c (g * h) l - c' (g * h) l)
        + (c g (h * l) - c' g (h * l)) - (c g h - c' g h)
      = (g • c h l - c (g * h) l + c g (h * l) - c g h)
        - (g • c' h l - c' (g * h) l + c' g (h * l) - c' g h) := by
    rw [smul_sub]; abel
  rw [key, h1, h2, sub_zero]

lemma isCocycle2_id_iff {c : G → G → M} :
    SSGRoute.IsCocycle2 (MonoidHom.id G) c ↔
      ∀ g h l : G, g • c h l - c (g * h) l + c g (h * l) - c g h = 0 := by
  simp only [SSGRoute.IsCocycle2, MonoidHom.id_apply]

lemma solve_b {a b c d : M} (h : a - b + c - d = 0) : b = a + c - d := by
  have h' : a - b + c = d := sub_eq_zero.mp h
  rw [← h']; abel

lemma solve_cc {a b c d : M} (h : a - b + c - d = 0) : c = d - a + b := by
  have h' : a - b + c = d := sub_eq_zero.mp h
  rw [← h']; abel

lemma solve_a {a b c d : M} (h : a - b + c - d = 0) : a = d - c + b := by
  have h' : a - b + c = d := sub_eq_zero.mp h
  rw [← h']; abel

lemma smul_eq_zero_of {g : G} {m : M} (h : g • m = 0) : m = 0 := by
  have h2 : g⁻¹ • (g • m) = g⁻¹ • (0 : M) := congrArg _ h
  rw [← mul_smul, inv_mul_cancel, one_smul, smul_zero] at h2
  exact h2

end Basic

/-! ## Averaging a crossed homomorphism over a finite group -/

section Average

variable {W : Type} [Group W] [Fintype W] {M : Type} [AddCommGroup M] {p : ℕ}
  [Fact p.Prime] [Module (ZMod p) M] [DistribMulAction W M] [SMulCommClass W (ZMod p) M]

/-- **Averaging a crossed homomorphism.**  If `f : W → M` satisfies
`f (a*b) = a • f b + f a` and `|W|` is invertible in `𝔽_p`, then `f` is the coboundary of the
average `γ := -|W|⁻¹ • ∑ f`, i.e. `f w = w • γ - γ` for all `w : W`. -/
lemma crossed_hom_average
    (hcop : Nat.Coprime (Fintype.card W) p) (f : W → M)
    (hf : ∀ a b : W, f (a * b) = a • f b + f a) :
    ∃ γ : M, γ = - ( (((Fintype.card W : ℕ) : ZMod p))⁻¹ • (∑ u : W, f u) ) ∧
      ∀ w : W, f w = w • γ - γ := by
  have hunit : IsUnit (((Fintype.card W : ℕ) : ZMod p)) :=
    (ZMod.isUnit_iff_coprime (Fintype.card W) p).mpr hcop
  have hne : (((Fintype.card W : ℕ) : ZMod p)) ≠ 0 := hunit.ne_zero
  have hcancel : ∀ x : M, (((Fintype.card W : ℕ) : ZMod p))⁻¹ • ((((Fintype.card W : ℕ) : ZMod p)) • x) = x := by
    intro x; rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  let S : M := ∑ u : W, f u
  let γ : M := - ( (((Fintype.card W : ℕ) : ZMod p))⁻¹ • S )
  refine ⟨γ, rfl, fun w => ?_⟩
  have hS : S = w • S + ((Fintype.card W : ℕ) : ZMod p) • f w := by
    show (∑ u : W, f u) = w • (∑ u : W, f u) + ((Fintype.card W : ℕ) : ZMod p) • f w
    calc (∑ u : W, f u) = ∑ u : W, f (w * u) := (Equiv.sum_comp (Equiv.mulLeft w) f).symm
      _ = ∑ u : W, (w • f u + f w) := Finset.sum_congr rfl (fun u _ => hf w u)
      _ = w • (∑ u : W, f u) + ∑ _u : W, f w := by
            rw [Finset.sum_add_distrib, Finset.smul_sum]
      _ = w • (∑ u : W, f u) + ((Fintype.card W : ℕ) : ZMod p) • f w := by
            rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hNsmul : (((Fintype.card W : ℕ) : ZMod p)) • f w = S - w • S := by
    nth_rewrite 1 [hS]; abel
  have hfw : f w = ((((Fintype.card W : ℕ) : ZMod p))⁻¹ • S) - w • ((((Fintype.card W : ℕ) : ZMod p))⁻¹ • S) := by
    rw [← hcancel (f w), hNsmul, smul_sub, (smul_comm w (((Fintype.card W : ℕ) : ZMod p))⁻¹ S).symm]
  show f w = w • γ - γ
  rw [show γ = - ( (((Fintype.card W : ℕ) : ZMod p))⁻¹ • S ) from rfl, hfw, smul_neg]; abel

end Average

/-- **Descent of a `2`-cocycle along a normal subgroup of order prime to `p` whose restriction is
a coboundary.**

`G` a group, `W ⊴ G` a finite normal subgroup with `Nat.Coprime (Nat.card W) p` (`hcop`),
`M` a finite `𝔽_p`-module on which `G` acts (`SMulCommClass G (ZMod p) M`).  If `c : G → G → M`
is a `2`-cocycle (`SSGRoute.IsCocycle2` with `act = id`) whose restriction to `W` is a coboundary
on `W` (witness `b`), then `c` differs from the inflation of a `2`-cocycle `c₀` on `G/W` (with
values in `M^W`) by a coboundary `δβ`:

the conclusion exhibits `β : G → M` and `c₀ : G ⧸ W → G ⧸ W → M` with
* `c₀` a `2`-cocycle on `G/W` for the representative-level action `(g : G) • _` (its values are
  `W`-fixed, so this is well defined on cosets),
* all values `c₀ x y` fixed by `W`,
* `c g h = (g • β h - β (g*h) + β g) + c₀ (mk g) (mk h)` for all `g h : G`.

This is the cochain-level form of the inflation–restriction exactness
`ker(H²(G,M) → H²(W,M)) = im(H²(G/W, M^W) → H²(G,M))`, which holds because `p ∤ |W|` and hence
`H^q(W,M) = 0` for `q ≥ 1` (averaging/Maschke).
Route: with `e := c - δβ` vanishing on `W × W` and `θ g := (1/|W|) Σ_{w ∈ W} e (g,w)` (the
average over `W`, whose order is invertible in `𝔽_p`) one checks `δθ (g,w) = e (g,w)` for all
`g : G`, `w ∈ W`, so that `e' := e - δθ` vanishes on `G × W`; then `e'` is right-`W`-invariant
and descends to a cocycle on `G/W` with values in `M^W`, explicitly
`c₀ (mk g) (mk h) := e' (g,h)`.  The multiplicativity of the action (`SMulCommClass`) is used in
the averaging step. -/
theorem descentInflationFinite
    (p : ℕ) [Fact p.Prime] {G : Type} [Group G] (W : Subgroup G) [W.Normal] [Finite W]
    (hcop : Nat.Coprime (Nat.card W) p)
    {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    (c : G → G → M) (hc : _root_.SSGRoute.IsCocycle2 (MonoidHom.id G) c)
    (hW : ∃ b : W → M, ∀ w w' : W, c (w : G) (w' : G) = (w : G) • b w' - b (w * w') + b w) :
    ∃ (β : G → M) (c₀ : G ⧸ W → G ⧸ W → M),
      (∀ g h l : G, (g : G) • c₀ (QuotientGroup.mk' W h) (QuotientGroup.mk' W l)
          - c₀ (QuotientGroup.mk' W (g * h)) (QuotientGroup.mk' W l)
          + c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W (h * l))
          - c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W h) = 0) ∧
      (∀ g h : G, ∀ w : W, (w : G) • c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W h)
          = c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W h)) ∧
      (∀ g h : G, c g h = (g • β h - β (g * h) + β g)
          + c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W h)) := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  have hcopF : Nat.Coprime (Fintype.card W) p := by
    rw [Fintype.card_eq_nat_card]; exact hcop
  obtain ⟨b, hb⟩ := hW
  let B : G → M := fun g => if hg : g ∈ W then b ⟨g, hg⟩ else 0
  have hB : ∀ w : W, B (w : G) = b w := fun w => dif_pos w.2
  let E₀ : G → G → M := fun g h => c g h - dlt B g h
  have hE₀coc : SSGRoute.IsCocycle2 (MonoidHom.id G) E₀ := coc_sub hc (dlt_cocycle B)
  have hE₀ : ∀ g h l : G, g • E₀ h l - E₀ (g * h) l + E₀ g (h * l) - E₀ g h = 0 :=
    isCocycle2_id_iff.mp hE₀coc
  have hE₀W : ∀ w w' : W, E₀ (w : G) (w' : G) = 0 := by
    intro w w'
    have h1 : E₀ (w : G) (w' : G) = c (w : G) (w' : G) - ((w : G) • b w' - b (w * w') + b w) := by
      show c (w : G) (w' : G) - dlt B (w : G) (w' : G)
        = c (w : G) (w' : G) - ((w : G) • b w' - b (w * w') + b w)
      rw [dlt, show ((w : G) * (w' : G)) = ((w * w' : W) : G) from rfl]
      simp only [hB]
    rw [h1, hb w w']; abel
  -- the first averaging `θ`, killing the `W`-dependence in the *second* variable
  let N : ℕ := Fintype.card W
  have hNne : (((N : ℕ) : ZMod p)) ≠ 0 := by
    have hunit : IsUnit (((N : ℕ) : ZMod p)) := (ZMod.isUnit_iff_coprime N p).mpr hcopF
    exact hunit.ne_zero
  let θ : G → M := fun g => (((N : ℕ) : ZMod p))⁻¹ • ∑ u : W, E₀ g (u : G)
  have hθW : ∀ w : W, θ (w : G) = 0 := by
    intro w
    show (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₀ (w : G) (u : G)) = 0
    rw [Finset.sum_eq_zero (fun u _ => hE₀W w u), smul_zero]
  have hθdiff : ∀ (g : G) (w : W), θ g - θ (g * (w : G)) = E₀ g (w : G) := by
    intro g w
    have h2 : ∀ u : W, E₀ (g * (w : G)) (u : G) = E₀ g ((w : G) * (u : G)) - E₀ g (w : G) := by
      intro u
      have hh := hE₀ g (w : G) (u : G)
      rw [hE₀W w u, smul_zero] at hh
      have hb' := solve_b hh
      rwa [zero_add] at hb'
    have hterm : ∀ u : W, E₀ g (u : G) - E₀ (g * (w : G)) (u : G)
        = E₀ g (u : G) - E₀ g ((w : G) * (u : G)) + E₀ g (w : G) := by
      intro u; rw [h2 u]; abel
    have hreindex : (∑ u : W, E₀ g ((w : G) * (u : G))) = ∑ u : W, E₀ g (u : G) := by
      have hcoe : (∑ u : W, E₀ g ((w : G) * (u : G))) = ∑ u : W, E₀ g (((w * u : W) : G)) :=
        Finset.sum_congr rfl (fun u _ => by rw [Subgroup.coe_mul])
      rw [hcoe]
      exact Equiv.sum_comp (Equiv.mulLeft w) (fun v : W => E₀ g (v : G))
    have hmain : (∑ u : W, E₀ g (u : G)) - (∑ u : W, E₀ (g * (w : G)) (u : G))
        = ((N : ℕ) : ZMod p) • E₀ g (w : G) := by
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl (fun u _ => hterm u)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hreindex]
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
      abel
    show (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₀ g (u : G))
        - (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₀ (g * (w : G)) (u : G)) = E₀ g (w : G)
    rw [← smul_sub, hmain, smul_smul, inv_mul_cancel₀ hNne, one_smul]
  let E₁ : G → G → M := fun g h => E₀ g h - dlt θ g h
  have hE₁coc : SSGRoute.IsCocycle2 (MonoidHom.id G) E₁ := coc_sub hE₀coc (dlt_cocycle θ)
  have hE₁ : ∀ g h l : G, g • E₁ h l - E₁ (g * h) l + E₁ g (h * l) - E₁ g h = 0 :=
    isCocycle2_id_iff.mp hE₁coc
  have hE₁W : ∀ g : G, ∀ w : W, E₁ g (w : G) = 0 := by
    intro g w
    have h1 : dlt θ g (w : G) = E₀ g (w : G) := by
      rw [dlt, hθW w, smul_zero]
      have h2 : (0 : M) - θ (g * (w : G)) + θ g = θ g - θ (g * (w : G)) := by abel
      rw [h2, hθdiff g w]
    show E₀ g (w : G) - dlt θ g (w : G) = 0
    rw [h1, sub_self]
  have hE₁invR : ∀ g h : G, ∀ w : W, E₁ g (h * (w : G)) = E₁ g h := by
    intro g h w
    have hh := hE₁ g h (w : G)
    rw [hE₁W h w, smul_zero, hE₁W (g * h) w] at hh
    have := solve_cc hh
    simpa using this
  have hE₁invL2 : ∀ (g : G) (w : W) (h : G), E₁ g ((w : G) * h) = E₁ g h := by
    intro g w h
    have hconj : h⁻¹ * (w : G) * h ∈ W := by
      have hx := Subgroup.Normal.conj_mem (inferInstance : W.Normal) (w : G) w.2 h⁻¹
      simpa [mul_assoc] using hx
    have hww : ((w : G) * h) = h * ((⟨h⁻¹ * (w : G) * h, hconj⟩ : W) : G) := by
      show (w : G) * h = h * (h⁻¹ * (w : G) * h); group
    rw [hww, hE₁invR g h ⟨h⁻¹ * (w : G) * h, hconj⟩]
  have hcross : ∀ (h : G) (a b : W),
      E₁ ((a * b : W) : G) h = (a : G) • E₁ (b : G) h + E₁ (a : G) h := by
    intro h a b
    have hh := hE₁ (a : G) (b : G) h
    rw [hE₁W a b, hE₁invL2 (a : G) b h, show ((a : G) * (b : G)) = ((a * b : W) : G) from rfl] at hh
    have := solve_b hh
    rw [sub_zero] at this
    exact this
  -- the second averaging `γ`, killing the `W`-dependence in the *first* variable
  let γ : G → M := fun h => - ( (((N : ℕ) : ZMod p))⁻¹ • ∑ u : W, E₁ (u : G) h )
  let E₂ : G → G → M := fun g h => E₁ g h - dlt γ g h
  have hE₂coc : SSGRoute.IsCocycle2 (MonoidHom.id G) E₂ := coc_sub hE₁coc (dlt_cocycle γ)
  have hE₂ : ∀ g h l : G, g • E₂ h l - E₂ (g * h) l + E₂ g (h * l) - E₂ g h = 0 :=
    isCocycle2_id_iff.mp hE₂coc
  have hγW : ∀ w : W, γ (w : G) = 0 := by
    intro w
    show - ( (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₁ (u : G) (w : G)) ) = 0
    simp only [hE₁W, Finset.sum_const_zero, smul_zero, neg_zero]
  have hγright : ∀ (g : G) (w : W), γ (g * (w : G)) = γ g := by
    intro g w
    have hsum : (∑ u : W, E₁ (u : G) (g * (w : G))) = ∑ u : W, E₁ (u : G) g :=
      Finset.sum_congr rfl (fun u _ => hE₁invR (u : G) g w)
    show - ( (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₁ (u : G) (g * (w : G))) )
      = - ( (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₁ (u : G) g) )
    rw [hsum]
  have hγleft : ∀ (h : G) (w : W), γ ((w : G) * h) = γ h := by
    intro h w
    have hsum : (∑ u : W, E₁ (u : G) ((w : G) * h)) = ∑ u : W, E₁ (u : G) h :=
      Finset.sum_congr rfl (fun u _ => hE₁invL2 (u : G) w h)
    show - ( (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₁ (u : G) ((w : G) * h)) )
      = - ( (((N : ℕ) : ZMod p))⁻¹ • (∑ u : W, E₁ (u : G) h) )
    rw [hsum]
  have hTate : ∀ (h : G) (w : W), E₁ (w : G) h = (w : G) • γ h - γ h := by
    intro h w
    have hf : ∀ a b : W, (fun u : W => E₁ (u : G) h) (a * b)
        = a • (fun u : W => E₁ (u : G) h) b + (fun u : W => E₁ (u : G) h) a := by
      intro a b
      show E₁ ((a * b : W) : G) h = (a : G) • E₁ (b : G) h + E₁ (a : G) h
      exact hcross h a b
    obtain ⟨gm, hgmdef, hgm⟩ := crossed_hom_average hcopF (fun u : W => E₁ (u : G) h) hf
    have hγeq : γ h = gm := by rw [hgmdef]
    rw [hγeq]
    exact hgm w
  have hE₂vanR : ∀ (g : G) (w : W), E₂ g (w : G) = 0 := by
    intro g w
    have h1 : dlt γ g (w : G) = 0 := by
      rw [dlt, hγW w, smul_zero, hγright g w]; abel
    show E₁ g (w : G) - dlt γ g (w : G) = 0
    rw [hE₁W g w, h1, sub_zero]
  have hE₂vanL : ∀ (h : G) (w : W), E₂ (w : G) h = 0 := by
    intro h w
    have h1 : dlt γ (w : G) h = E₁ (w : G) h := by
      rw [dlt, hγW w, hγleft h w, hTate h w]; abel
    show E₁ (w : G) h - dlt γ (w : G) h = 0
    rw [h1, sub_self]
  have hE₂invR : ∀ (g h : G) (w : W), E₂ g (h * (w : G)) = E₂ g h := by
    intro g h w
    have h1 : dlt γ g (h * (w : G)) = dlt γ g h := by
      have harg2 : γ (h * (w : G)) = γ h := hγright h w
      have harg : γ (g * (h * (w : G))) = γ (g * h) := by
        rw [← mul_assoc, hγright (g * h) w]
      rw [dlt, dlt, harg2, harg]
    show E₁ g (h * (w : G)) - dlt γ g (h * (w : G)) = E₁ g h - dlt γ g h
    rw [hE₁invR g h w, h1]
  have hE₂invL2 : ∀ (g : G) (w : W) (h : G), E₂ g ((w : G) * h) = E₂ g h := by
    intro g w h
    have hconj : h⁻¹ * (w : G) * h ∈ W := by
      have hx := Subgroup.Normal.conj_mem (inferInstance : W.Normal) (w : G) w.2 h⁻¹
      simpa [mul_assoc] using hx
    have hww : ((w : G) * h) = h * ((⟨h⁻¹ * (w : G) * h, hconj⟩ : W) : G) := by
      show (w : G) * h = h * (h⁻¹ * (w : G) * h); group
    rw [hww, hE₂invR g h ⟨h⁻¹ * (w : G) * h, hconj⟩]
  have hE₂invR1 : ∀ (g : G) (w : W) (h : G), E₂ (g * (w : G)) h = E₂ g h := by
    intro g w h
    have hh := hE₂ g (w : G) h
    rw [hE₂vanL h w, hE₂vanR g w, hE₂invL2 g w h] at hh
    have := solve_b hh
    simpa using this
  have hE₂fix : ∀ (g h : G) (w : W), (w : G) • E₂ g h = E₂ g h := by
    intro g h w
    have hh := hE₂ (w : G) g h
    rw [hE₂vanL (g * h) w, hE₂vanL g w] at hh
    have hcong : E₂ ((w : G) * g) h = E₂ g h := by
      have hconj : g⁻¹ * (w : G) * g ∈ W := by
        have hx := Subgroup.Normal.conj_mem (inferInstance : W.Normal) (w : G) w.2 g⁻¹
        simpa [mul_assoc] using hx
      have hww : ((w : G) * g) = g * ((⟨g⁻¹ * (w : G) * g, hconj⟩ : W) : G) := by
        show (w : G) * g = g * (g⁻¹ * (w : G) * g); group
      rw [hww, hE₂invR1 g ⟨g⁻¹ * (w : G) * g, hconj⟩ h]
    have ha := solve_a hh
    rw [hcong] at ha
    simpa using ha
  -- the descended cocycle on `G ⧸ W`
  let c₀ : G ⧸ W → G ⧸ W → M := fun x y => E₂ (Quotient.out x) (Quotient.out y)
  have hc₀ : ∀ g h : G, c₀ (QuotientGroup.mk' W g) (QuotientGroup.mk' W h) = E₂ g h := by
    intro g h
    have hg : ∃ z ∈ W, g * z = Quotient.out (QuotientGroup.mk' W g) := by
      refine (QuotientGroup.mk'_eq_mk' W).mp ?_
      conv_rhs => rw [QuotientGroup.mk'_apply, QuotientGroup.out_eq']
    have hh : ∃ z ∈ W, h * z = Quotient.out (QuotientGroup.mk' W h) := by
      refine (QuotientGroup.mk'_eq_mk' W).mp ?_
      conv_rhs => rw [QuotientGroup.mk'_apply, QuotientGroup.out_eq']
    obtain ⟨z, hzW, hgz⟩ := hg
    obtain ⟨z', hz'W, hgz'⟩ := hh
    show E₂ (Quotient.out (QuotientGroup.mk' W g)) (Quotient.out (QuotientGroup.mk' W h)) = E₂ g h
    rw [← hgz, ← hgz', hE₂invR (g * z) h ⟨z', hz'W⟩, hE₂invR1 g ⟨z, hzW⟩ h]
  refine ⟨B + θ + γ, c₀, ?_, ?_, ?_⟩
  · intro g h l
    rw [hc₀ h l, hc₀ (g * h) l, hc₀ g (h * l), hc₀ g h]
    exact hE₂ g h l
  · intro g h w
    rw [hc₀ g h]
    exact hE₂fix g h w
  · intro g h
    rw [hc₀ g h]
    show c g h = dlt (B + θ + γ) g h + E₂ g h
    have hdl : dlt (B + θ + γ) g h = dlt B g h + dlt θ g h + dlt γ g h := by
      rw [dlt_add, dlt_add]
    have h0 : E₀ g h = c g h - dlt B g h := rfl
    have h1 : E₁ g h = E₀ g h - dlt θ g h := rfl
    have h2 : E₂ g h = E₁ g h - dlt γ g h := rfl
    rw [hdl, h2, h1, h0]; abel

end Work.SSGRoute

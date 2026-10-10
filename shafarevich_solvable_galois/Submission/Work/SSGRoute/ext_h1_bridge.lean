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
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
import Submission.Work.SSGRoute.bridge_mem_B2_isCoboundary2On
import Submission.Work.SSGRoute.cohomology_bridge
import Submission.Work.SSGRoute.h1_equiv_of_equiv
import Submission.Work.SSGRoute.homCoind_H0_restrict_ker_conj
import Submission.Work.SSGRoute.homCoind_H1_free_conj_v2
import Submission.Work.SSGRoute.homRep_unitsK_formula
import Submission.Work.SSGRoute.homRep_unitsK_formula_natural
import Submission.Work.SSGRoute.selfdual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_EXT.md (the lead's Ext-core design for Poitou–Tate) + DESIGN_PT.md. Definitions: Submission/Work/SSGRoute/PTDefs.lean (namespace SSGRoute.PTExt; do NOT edit). NK.* CFT library available. Siblings run in parallel.

# E1c `ext_h1_bridge` — `H¹(k,E) ≅ Ext¹_G(E', Kˣ)` -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

universe u v

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct
open scoped Classical
open Filter
open scoped Topology

/-! ## Generic exactness lemmas -/

section Generic

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

/-- **Ext side.** For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with `X₂` projective, the
connecting map `Ext⁰(X₁,Y) → Ext¹(X₃,Y)` is surjective with kernel the image of the map
`Ext⁰(X₂,Y) → Ext⁰(X₁,Y)`. -/
theorem ext_connecting_range_ker {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    [Projective S.X₂] :
    (hS.extClass.precomp Y (by norm_num : 1 + 0 = 1)).range = ⊤ ∧
    (hS.extClass.precomp Y (by norm_num : 1 + 0 = 1)).ker =
      ((Abelian.Ext.mk₀ S.f).precomp Y (by norm_num : 0 + 0 = 0)).range := by
  haveI : Subsingleton (Abelian.Ext S.X₂ Y 1) := Abelian.Ext.subsingleton_of_projective S.X₂ Y 0
  constructor
  · rw [AddMonoidHom.range_eq_top]
    intro y
    have hzero : (Abelian.Ext.mk₀ S.g).comp y (zero_add 1) = 0 := Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y y hzero
      (n₀ := 0) (by norm_num : 1 + 0 = 1)
    exact ⟨x, by simpa using hx⟩
  · apply le_antisymm
    · intro x hx
      rw [AddMonoidHom.mem_ker] at hx
      obtain ⟨w, hw⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y x
        (n₁ := 1) (by norm_num : 1 + 0 = 1) hx
      exact ⟨w, by simpa using hw⟩
    · rintro x ⟨w, rfl⟩
      rw [AddMonoidHom.mem_ker]
      simpa using hS.extClass_comp_assoc (Y := Y) w

end Generic

/-- **Cohomology side.** For a short exact sequence `0 → M → N → P → 0` of discrete `G`-modules
with `H¹(G,N) = 0`, the connecting map `δ : H⁰(G,P) → H¹(G,M)` is surjective with kernel the image
of `H⁰(G,N) → H⁰(G,P)`. -/
theorem coh_connecting_range_ker {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    [Subsingleton (Work.AbsoluteKummer.H1 G N)] :
    S.delta.range = ⊤ ∧
      S.delta.ker = (Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant).range := by
  have hzero : Work.AbsoluteKummer.mapH1 S.iota S.iota_equivariant = 0 :=
    AddMonoidHom.ext (fun x => Subsingleton.elim _ _)
  constructor
  · have h : S.delta.range = (Work.AbsoluteKummer.mapH1 S.iota S.iota_equivariant).ker :=
      le_antisymm S.range_delta_le_ker_mapH1 (Work.AbsoluteKummer.SES.ker_mapH1_le_range_delta S)
    rw [h, hzero, AddMonoidHom.ker_zero]
  · exact le_antisymm (Work.AbsoluteKummer.SES.ker_le_range_mapH0 S) S.range_mapH0_le_ker_delta

/-! ## The units of `Ω` as a discrete Galois module -/






/-! ## The action on `Ωˣ` and Hilbert 90 for `Gal(Ω/K)` -/



section H90
variable {kk : Type} [Field kk] {ΩΩ : Type} [Field ΩΩ] [Algebra kk ΩΩ] [IsGalois kk ΩΩ]

/-- Noether's Hilbert 90 for `Gal(Ω/K)`: a locally constant crossed homomorphism into `Ωˣ` is a
coboundary. -/
theorem exists_div_gal_omega (f : (ΩΩ ≃ₐ[kk] ΩΩ) → ΩΩˣ)
    (hf : ∀ σ τ : ΩΩ ≃ₐ[kk] ΩΩ, f (σ * τ) = f σ * umap kk ΩΩ σ (f τ))
    (hc : Work.AbsoluteKummer.IsLocallyConstant f) :
    ∃ b : ΩΩˣ, ∀ σ : ΩΩ ≃ₐ[kk] ΩΩ, f σ = umap kk ΩΩ σ b / b := by
  have hf1 : f 1 = 1 := by
    have h := hf 1 1
    rw [one_mul, umap_one] at h
    exact mul_left_cancel (by rw [mul_one]; exact h.symm)
  obtain ⟨U, hUopen, h1U, hUc⟩ := hc 1
  have hfU : ∀ y ∈ U, f y = 1 := fun y hy => by rw [hUc y hy, hf1]
  have hUn : U ∈ 𝓝 (1 : ΩΩ ≃ₐ[kk] ΩΩ) := hUopen.mem_nhds h1U
  haveI hNor : Normal kk ΩΩ := IsGalois.to_normal
  obtain ⟨M, hMfin, hMnorm, hMsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal kk ΩΩ U).mp hUn
  haveI := hMfin
  haveI := hMnorm
  have hker : (AlgEquiv.restrictNormalHom (F := kk) (K₁ := ΩΩ) ↥M).ker = M.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker M
  have hNnormal : M.fixingSubgroup.Normal := by
    rw [← hker]; exact MonoidHom.normal_ker _
  have hfN : ∀ n ∈ M.fixingSubgroup, f n = 1 := fun n hn => hfU n (hMsub hn)
  have hNinv : ∀ (a n : ΩΩ ≃ₐ[kk] ΩΩ), n ∈ M.fixingSubgroup → f (a * n) = f a := by
    intro a n hn
    rw [hf a n, hfN n hn, map_one, mul_one]
  have hmem : ∀ a : ΩΩ ≃ₐ[kk] ΩΩ, (f a : ΩΩ) ∈ M := by
    intro a
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
    intro n hn
    show n (f a : ΩΩ) = (f a : ΩΩ)
    have h1 : umap kk ΩΩ n (f a) = f (n * a) := by rw [hf n a, hfN n hn, one_mul]
    have h2 : f (n * a) = f a := by
      have heq : n * a = a * (a⁻¹ * n * a) := by group
      rw [heq, hNinv a (a⁻¹ * n * a) (hNnormal.conj_mem n hn a⁻¹)]
    have h3 := (umap_coe kk ΩΩ n (f a)).symm
    rw [h1, h2] at h3
    exact h3
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := kk) (K₁ := ΩΩ) ↥M) :=
    AlgEquiv.restrictNormalHom_surjective ΩΩ
  let lift : (↥M ≃ₐ[kk] ↥M) → (ΩΩ ≃ₐ[kk] ΩΩ) := fun χ => Classical.choose (hsurj χ)
  have hlift : ∀ χ, AlgEquiv.restrictNormalHom (F := kk) (K₁ := ΩΩ) ↥M (lift χ) = χ :=
    fun χ => Classical.choose_spec (hsurj χ)
  have happ : ∀ (χ : ↥M ≃ₐ[kk] ↥M) (x : ↥M),
      (((χ x) : ↥M) : ΩΩ) = (lift χ) (x : ΩΩ) := by
    intro χ x
    conv_lhs => rw [← hlift χ]
    exact AlgEquiv.restrictNormalHom_apply (F := kk) (K₁ := ΩΩ) M (lift χ) x
  let g : (↥M ≃ₐ[kk] ↥M) → (↥M)ˣ := fun χ =>
    Units.mk0 ⟨(f (lift χ) : ΩΩ), hmem (lift χ)⟩ (by
      intro h0
      have h1 : (f (lift χ) : ΩΩ) = 0 := congrArg (fun x : ↥M => (x : ΩΩ)) h0
      exact Units.ne_zero (f (lift χ)) h1)
  have hgcoc : ∀ χ ψ,
      ((g (χ * ψ) : (↥M)ˣ) : ↥M) = ((g χ : (↥M)ˣ) : ↥M) * χ ((g ψ : (↥M)ˣ) : ↥M) := by
    intro χ ψ
    apply Subtype.ext
    have hK : (f (lift (χ * ψ)) : ΩΩ) =
        (f (lift χ) : ΩΩ) * (lift χ) (f (lift ψ) : ΩΩ) := by
      have hn : (lift (χ * ψ))⁻¹ * (lift χ * lift ψ) ∈ M.fixingSubgroup := by
        rw [← hker, MonoidHom.mem_ker]
        simp only [map_mul, map_inv, hlift]
        group
      have hA : f (lift (χ * ψ)) = f (lift χ * lift ψ) := by
        have h := hNinv (lift (χ * ψ)) ((lift (χ * ψ))⁻¹ * (lift χ * lift ψ)) hn
        have heq : lift (χ * ψ) * ((lift (χ * ψ))⁻¹ * (lift χ * lift ψ)) =
            lift χ * lift ψ := by group
        rw [heq] at h
        exact h.symm
      rw [hA, hf (lift χ) (lift ψ)]
      rfl
    simp only [g, Units.val_mk0, Subtype.coe_mk] at hK ⊢
    push_cast
    rw [hK]
    congr 1
    push_cast
    exact (happ χ ⟨(f (lift ψ) : ΩΩ), hmem (lift ψ)⟩).symm
  obtain ⟨β, hβ⟩ := Work.AbsoluteKummer.exists_algEquiv_div_of_isCrossedHom g hgcoc
  refine ⟨Units.map (algebraMap ↥M ΩΩ).toMonoidWithZeroHom β, fun σ => ?_⟩
  set χ := AlgEquiv.restrictNormalHom (F := kk) (K₁ := ΩΩ) ↥M σ with hχ
  have hmemσ : (lift χ)⁻¹ * σ ∈ M.fixingSubgroup := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hlift, hχ]
    group
  have hσ : f σ = f (lift χ) := by
    conv_lhs => rw [show σ = lift χ * ((lift χ)⁻¹ * σ) by group]
    rw [hf (lift χ) ((lift χ)⁻¹ * σ), hfN ((lift χ)⁻¹ * σ) hmemσ, map_one, mul_one]
  rw [hσ]
  apply Units.ext
  have hL : (f (lift χ) : ΩΩ) = algebraMap ↥M ΩΩ ((g χ : (↥M)ˣ) : ↥M) := rfl
  have h := congrArg (algebraMap ↥M ΩΩ) (hβ χ)
  simp only [map_div₀] at h
  rw [hL, h, Units.val_div_eq_div_val]
  congr 1
  · rw [show ((umap kk ΩΩ σ (Units.map (algebraMap ↥M ΩΩ).toMonoidWithZeroHom β) : ΩΩˣ) : ΩΩ) =
        σ (Units.val (Units.map (algebraMap ↥M ΩΩ).toMonoidWithZeroHom β)) from umap_coe kk ΩΩ _ _]
    rw [show Units.val (Units.map (algebraMap ↥M ΩΩ).toMonoidWithZeroHom β) = ((↑β : ↥M) : ΩΩ) from by
      rw [Units.coe_map]; rfl]
    exact AlgEquiv.restrictNormalHom_apply M σ (↑β : ↥M)

end H90


section EAct

/-- The `Gal(Ω/k)`-action on `E` through `Gal(K/k)`. -/
noncomputable def resActE (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (E : Type) [AddCommGroup E]
    [DistribMulAction (K ≃ₐ[k] K) E] : DistribMulAction (Ω ≃ₐ[k] Ω) E where
  smul σ e := (SSGRoute.res k K σ) • e
  one_smul e := by
    show (SSGRoute.res k K 1) • e = e
    rw [map_one]; exact one_smul _ e
  mul_smul σ τ e := by
    show (SSGRoute.res k K (σ * τ)) • e = (SSGRoute.res k K σ) • (SSGRoute.res k K τ) • e
    rw [map_mul]; exact mul_smul _ _ e
  smul_zero σ := smul_zero _
  smul_add σ e e' := smul_add _ _ _

end EAct





attribute [local instance 10000] homCoind.instDistribMulActionAlgEquiv

/-! ## Forcing the conjugation action on `homCoind`

`homCoind k Ω K M` is an abbreviation for `M.V →+ Additive Ωˣ`, so type class search sometimes
finds the *pointwise* `DistribMulAction` on `AddMonoidHom` (`(σ • φ) x = σ • φ x`) rather than the
conjugation action `(σ • φ) x = σ • φ (σ⁻¹ • x)` defined in `homCoindDefs`.  Every lemma of the
`homCoind` chapter (`homRep_unitsK_formula`, `homCoind_H0_restrict_ker`, …) is stated for the
conjugation action, so we re-declare it here at high priority: in this file both `H⁰` and `•`
then always mean the conjugation action. -/



/-! ## Auxiliary `Ext`-calculus -/

section ExtCalc

/-- The canonical identification `Ext⁰(X,Y) ≃+ (X ⟶ Y)` sends `mk₀ f` back to `f`. -/
lemma ext_addEquiv₀_mk₀_ehb {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y : C}
    (f : X ⟶ Y) :
    Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f) = f :=
  (Abelian.Ext.mk₀_bijective X Y).1 (by rw [Abelian.Ext.mk₀_addEquiv₀_apply])

/-- Precomposition with `mk₀ u` on `Ext⁰` is precomposition with `u` on morphisms. -/
lemma ext_precomp_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y Z : C}
    (u : X ⟶ Y) (f : Y ⟶ Z) :
    (Abelian.Ext.mk₀ u).precomp Z (by norm_num : 0 + 0 = 0) (Abelian.Ext.mk₀ f) =
      Abelian.Ext.mk₀ (u ≫ f) := by
  change (Abelian.Ext.mk₀ u).comp (Abelian.Ext.mk₀ f) (zero_add 0) = Abelian.Ext.mk₀ (u ≫ f)
  exact Abelian.Ext.mk₀_comp_mk₀ u f

end ExtCalc

/-! ## Bridging the cocycle predicates with the cohomology groups -/

section CohBridge2

/-- A cocycle which is invariant under an open subgroup is a continuous `1`-cocycle. -/
lemma mem_absZ1_of_isCocycleOn_isLocConstOn {Γ G M : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [Group G] [AddCommGroup M] [DistribMulAction G M] (act : Γ →* G)
    {b : Γ → M} (hb : SSGRoute.IsCocycleOn act ⊤ b)
    (hl : SSGRoute.IsLocConstOn (⊤ : Subgroup Γ) b) :
    b ∈ @Work.AbsoluteKummer.Z1 Γ M _ _ _ (DistribMulAction.compHom M act) := by
  show b ∈ (@Work.GroupCohomology.Z1 Γ M _ _ (DistribMulAction.compHom M act)) ⊓
    Work.AbsoluteKummer.C1c Γ M
  exact ⟨(isCocycleOn_iff_mem_Z1 act b).mp hb,
    Work.SSGRoute.top_isLocallyConstant_of_isLocConstOn hl⟩

/-- `b ∈ B¹` iff its class in `Z¹` vanishes. -/
lemma mem_absB1_iff_exists {Γ M : Type} [TopologicalSpace Γ] [Group Γ] [AddCommGroup M]
    [DistribMulAction Γ M] (b : Γ → M) :
    b ∈ Work.AbsoluteKummer.B1 Γ M ↔
      ∃ (hf : b ∈ Work.GroupCohomology.Z1 Γ M),
        Work.GroupCohomology.H1π Γ M ⟨b, hf⟩ = 0 := by
  show b ∈ Work.GroupCohomology.B1 Γ M ↔ _
  constructor
  · intro hb
    have hbZ := Work.GroupCohomology.B1_le_Z1 Γ M hb
    exact ⟨hbZ, (h1pi_eq_zero_iff ⟨b, hbZ⟩).mpr hb⟩
  · rintro ⟨hf, h0⟩
    exact (h1pi_eq_zero_iff ⟨b, hf⟩).mp h0

end CohBridge2

/-! ## The duality `E ≃+ Hom(E^∨(1), Ωˣ)` in `homCoind` shape -/

section Duality

/-- `dualPairingEquiv` in the shape needed by the assembly: an equivariant additive isomorphism
`E ≃+ homCoind k Ω K (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗ T)))`. -/
theorem dualPairingEquiv_homCoind (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ∃ Φ : E ≃+ homCoind k Ω K (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))),
      ∀ (σ : Ω ≃ₐ[k] Ω) (e : E), Φ ((SSGRoute.res k K σ) • e) = σ • Φ e := by
  obtain ⟨Φ, hΦ⟩ := SelfDual.dualPairingEquiv p k Ω K ζ hζ hζK T hT E
  exact ⟨Φ, fun σ e => by
    apply AddMonoidHom.ext
    intro x
    rw [homCoind.smul_apply]
    exact hΦ σ e x⟩

end Duality

/-! ## The target -/

/-- **E1c.** `H¹(k, E) ≅ Ext¹_{Gal(K/k)}(E', Kˣ)` for `E' = DualMod p (E ⊗ T) = E^∨(1)`
(Hochschild–Serre for `Ext_{G_k}(E', Ω̄ˣ)` with Hilbert 90): there is a map from continuous
`1`-cochains of `G_k` to `Ext¹_G(E', Kˣ)`, additive on cocycles, whose kernel on cocycles is the
coboundaries and which is onto. -/
theorem ext_h1_bridge (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ∃ β : ((Ω ≃ₐ[k] Ω) → E) →
        Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (unitsK k K) 1,
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
          β (b + b') = β b + β b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b)) ∧
      ∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
        SSGRoute.IsLocConstOn ⊤ b ∧ β b = y := by
  classical
  -- ===== the Ext side =====
  let E' : Type := DualMod p (E ⊗[ZMod p] T)
  haveI hNp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hTf : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  haveI hATf : Module.Finite (ZMod p) (E ⊗[ZMod p] T) :=
    Module.Finite.tensorProduct (ZMod p) E T
  haveI hE'fin : Finite E' :=
    (Module.finite_iff_finite (R := ZMod p)).mp
      (Module.Finite.linearMap (ZMod p) (ZMod p) (E ⊗[ZMod p] T) (ZMod p))
  let F : Rep.{0} Coeff (K ≃ₐ[k] K) := Rep.free Coeff (K ≃ₐ[k] K) E'
  let X3 : Rep.{0} Coeff (K ≃ₐ[k] K) := modRep (K ≃ₐ[k] K) E'
  let pic : F ⟶ X3 := Rep.freeLift Coeff (K ≃ₐ[k] K) X3 (fun e => e)
  have hpic : Epi pic := by
    rw [Rep.epi_iff_surjective]
    intro a
    refine ⟨Finsupp.single a (MonoidAlgebra.single 1 1), ?_⟩
    show Rep.Hom.hom pic (Finsupp.single a (MonoidAlgebra.single 1 1)) = a
    rw [show Rep.Hom.hom pic = Representation.freeLift X3.ρ (fun e => e) from rfl]
    erw [Representation.freeLift_single_single]
    simp only [map_one]
    exact one_smul _ a
  let S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)) :=
    ShortComplex.mk (Limits.kernel.ι pic) pic (Limits.kernel.condition pic)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel pic) inferInstance hpic
  have hExt := ext_connecting_range_ker hS (unitsK k K)
  -- the connecting map `Ext⁰(R,Kˣ) ↠ Ext¹(E',Kˣ)` and its kernel
  let ΦE : Abelian.Ext S.X₁ (unitsK k K) 0 →+ Abelian.Ext X3 (unitsK k K) 1 :=
    hS.extClass.precomp (unitsK k K) (by norm_num : 1 + 0 = 1)
  have hΦEsurj : Function.Surjective ΦE := (AddMonoidHom.range_eq_top).mp hExt.1
  let pre : Abelian.Ext S.X₂ (unitsK k K) 0 →+ Abelian.Ext S.X₁ (unitsK k K) 0 :=
    (Abelian.Ext.mk₀ S.f).precomp (unitsK k K) (by norm_num : 0 + 0 = 0)
  have hΦEker : ΦE.ker = pre.range := hExt.2
  -- ===== the cohomology side =====
  have hfsurj : Function.Surjective (Rep.Hom.hom pic) := (Rep.epi_iff_surjective pic).mp hpic
  let uHom : S.X₁.V →+ S.X₂.V :=
    { toFun := fun x => Rep.Hom.hom S.f x
      map_zero' := map_zero (Rep.Hom.hom S.f)
      map_add' := fun a b => map_add (Rep.Hom.hom S.f) a b }
  let gFun : homCoind k Ω K S.X₂ →+ homCoind k Ω K S.X₁ :=
    { toFun := fun φ => φ.comp uHom
      map_zero' := by ext x; rfl
      map_add' := by intro a b; ext x; rfl }
  have hG : ∀ (ψ : homCoind k Ω K S.X₂) (y : S.X₁.V),
      gFun ψ y = ψ (Rep.Hom.hom S.f y) := fun ψ y => rfl
  have gFun_mem : ∀ φ ∈ (@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)),
      gFun φ ∈ (@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) := by
    intro φ hφ
    intro σ
    apply AddMonoidHom.ext
    intro x
    rw [show (σ • (gFun φ)) x
        = homCoind.smulHom (k := k) (Ω := Ω) σ
            ((gFun φ) (S.X₁.ρ ((SSGRoute.res k K) σ)⁻¹ x)) from rfl]
    have h1 : gFun φ (S.X₁.ρ ((SSGRoute.res k K) σ)⁻¹ x)
        = φ (S.X₂.ρ ((SSGRoute.res k K) σ)⁻¹ (Rep.Hom.hom S.f x)) := by
      rw [hG, Rep.hom_comm_apply]
    have h3 : homCoind.smulHom (k := k) (Ω := Ω) σ
          ((gFun φ) (S.X₁.ρ ((SSGRoute.res k K) σ)⁻¹ x))
        = homCoind.smulHom (k := k) (Ω := Ω) σ
            (φ (S.X₂.ρ ((SSGRoute.res k K) σ)⁻¹ (Rep.Hom.hom S.f x))) := by
      rw [h1]
    have h2 : homCoind.smulHom (k := k) (Ω := Ω) σ
          (φ (S.X₂.ρ ((SSGRoute.res k K) σ)⁻¹ (Rep.Hom.hom S.f x)))
        = φ (Rep.Hom.hom S.f x) :=
      DFunLike.congr_fun (hφ σ) (Rep.Hom.hom S.f x)
    rw [h3, h2]
    exact (hG φ x).symm
  let g : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)) →+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) :=
    (gFun.comp (AddSubgroup.subtype _)).codRestrict _ (fun φ => gFun_mem φ.1 φ.2)
  have hg : ∀ (ψ : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)))
      (x : S.X₁.V), Subtype.val (g ψ) x = Subtype.val ψ (Rep.Hom.hom S.f x) := by
    intro ψ x
    exact hG (ψ : homCoind k Ω K S.X₂) x
  haveI hsub : Subsingleton (@Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) E')) _ _
      (homCoind.instAddCommGroup (Rep.free Coeff (K ≃ₐ[k] K) E'))
      (homCoind.instDistribMulActionAlgEquiv (Rep.free Coeff (K ≃ₐ[k] K) E'))) :=
    homCoind_H1_free_conj_v2 (k := k) (Ω := Ω) (K := K) (ι := E')
  obtain ⟨δ, hδsurj, hδker⟩ :=
    homCoind_H0_restrict_ker_conj (k := k) (Ω := Ω) (K := K) (ι := E') pic hfsurj g hg
  -- ===== the two `H⁰`'s are the same =====
  obtain ⟨ΦR, hΦR⟩ := homRep_unitsK_formula (k := k) (Ω := Ω) (K := K) S.X₁
  obtain ⟨ΦF, hΦF⟩ := homRep_unitsK_formula (k := k) (Ω := Ω) (K := K) S.X₂
  have hnat := homRep_unitsK_formula_natural (k := k) (Ω := Ω) (K := K) S.f ΦR ΦF hΦR hΦF g hg
  let ΨR : Abelian.Ext S.X₁ (unitsK k K) 0 ≃+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) :=
    (Abelian.Ext.addEquiv₀).trans ΦR
  let ΨF : Abelian.Ext S.X₂ (unitsK k K) 0 ≃+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)) :=
    (Abelian.Ext.addEquiv₀).trans ΦF
  have hpre1 : ∀ f : S.X₂ ⟶ unitsK k K,
      pre (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (S.f ≫ f) := by
    intro f
    change (Abelian.Ext.mk₀ S.f).precomp (unitsK k K) (by norm_num : 0 + 0 = 0)
        (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (S.f ≫ f)
    rw [ext_precomp_mk₀]
  have hΨR : ∀ f : S.X₁ ⟶ unitsK k K, ΨR (Abelian.Ext.mk₀ f) = ΦR f := by
    intro f
    show ΦR (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f)) = ΦR f
    rw [ext_addEquiv₀_mk₀_ehb]
  have hΨF : ∀ f : S.X₂ ⟶ unitsK k K, ΨF (Abelian.Ext.mk₀ f) = ΦF f := by
    intro f
    show ΦF (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f)) = ΦF f
    rw [ext_addEquiv₀_mk₀_ehb]
  have hpre : ∀ x : Abelian.Ext S.X₂ (unitsK k K) 0, ΨR (pre x) = g (ΨF x) := by
    intro x
    rw [show x = Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ x) from
      (Abelian.Ext.mk₀_addEquiv₀_apply x).symm]
    rw [hpre1 (Abelian.Ext.addEquiv₀ x), hΨR (S.f ≫ Abelian.Ext.addEquiv₀ x),
      hΨF (Abelian.Ext.addEquiv₀ x)]
    exact hnat (Abelian.Ext.addEquiv₀ x)
  have hmap : AddSubgroup.map ΨR.toAddMonoidHom ΦE.ker = δ.ker := by
    rw [hΦEker, hδker]
    have h1 : AddSubgroup.map ΨR.toAddMonoidHom pre.range =
        (ΨR.toAddMonoidHom.comp pre).range := by
      rw [AddMonoidHom.range_eq_map pre, AddSubgroup.map_map,
        ← AddMonoidHom.range_eq_map (ΨR.toAddMonoidHom.comp pre)]
    rw [h1]
    have h2 : ΨR.toAddMonoidHom.comp pre = g.comp ΨF.toAddMonoidHom := by
      apply AddMonoidHom.ext
      intro y
      exact hpre y
    rw [h2, AddMonoidHom.range_eq_map (g.comp ΨF.toAddMonoidHom), ← AddSubgroup.map_map,
      ← AddMonoidHom.range_eq_map ΨF.toAddMonoidHom,
      (AddMonoidHom.range_eq_top).mpr ΨF.surjective]
    exact (AddMonoidHom.range_eq_map g).symm
  -- ===== collecting the isomorphism `Ext¹ ≃+ H¹(Γ, homCoind (E'))` =====
  let e1 : Abelian.Ext S.X₁ (unitsK k K) 0 ⧸ ΦE.ker ≃+ Abelian.Ext X3 (unitsK k K) 1 :=
    QuotientAddGroup.quotientKerEquivOfSurjective ΦE hΦEsurj
  let e2 : Abelian.Ext S.X₁ (unitsK k K) 0 ⧸ ΦE.ker ≃+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) ⧸ δ.ker :=
    QuotientAddGroup.congr _ _ ΨR hmap
  let e3 : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) ⧸ δ.ker ≃+
      @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K X3) _ _
          (homCoind.instAddCommGroup X3) (homCoind.instDistribMulActionAlgEquiv X3) :=
    QuotientAddGroup.quotientKerEquivOfSurjective δ hδsurj
  have hExtHomCoind : Abelian.Ext X3 (unitsK k K) 1 ≃+
      @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K X3) _ _
          (homCoind.instAddCommGroup X3) (homCoind.instDistribMulActionAlgEquiv X3) :=
    e1.symm.trans (e2.trans e3)
  -- ===== the coefficient change `H¹(Γ,E) ≃+ H¹(Γ, homCoind (E'))` =====
  obtain ⟨Φd, hΦd⟩ := dualPairingEquiv_homCoind p k Ω K ζ hζ hζK T hT E
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  obtain ⟨e0⟩ := h1_equiv_of_equiv Φd hΦd
  let Ψ : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) E ≃+ Abelian.Ext X3 (unitsK k K) 1 :=
    e0.trans hExtHomCoind.symm
  -- ===== the map `β` =====
  let β : ((Ω ≃ₐ[k] Ω) → E) → Abelian.Ext X3 (unitsK k K) 1 := fun b =>
    if h : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E then
      Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, h⟩)
    else 0
  have hβ_eq : ∀ z : Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E,
      β z.1 = Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E z) := by
    intro z
    exact dif_pos z.2
  refine ⟨β, ?_, ?_, ?_⟩
  · intro b b' hb hbl hb' hbl'
    have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hbl
    have hbZ' : b' ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb' hbl'
    have hbbZ : b + b' ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E).add_mem hbZ hbZ'
    have h1 : β (b + b') = Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b + b', hbbZ⟩) :=
      dif_pos hbbZ
    have h2 : β b = Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) := dif_pos hbZ
    have h3 : β b' = Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b', hbZ'⟩) := dif_pos hbZ'
    have hπ : Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b + b', hbbZ⟩
        = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩
          + Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b', hbZ'⟩ := by
      rw [show (⟨b + b', hbbZ⟩ : Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E) =
          ⟨b, hbZ⟩ + ⟨b', hbZ'⟩ from Subtype.ext rfl, map_add]
    rw [h1, h2, h3, hπ]
    exact map_add Ψ _ _
  · intro b hb hbl
    have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
      mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hbl
    have h1 : β b = Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) := dif_pos hbZ
    rw [h1, show Ψ (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) = 0 ↔
        Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩ = 0 from Ψ.map_eq_zero_iff]
    rw [Work.AbsoluteKummer.H1π_eq_zero_iff]
    rw [mem_absB1_iff_exists]
    exact (isCoboundaryOn_top_iff_class_eq_zero (SSGRoute.res k K) b).symm
  · intro y
    obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) E).comap
        (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E).subtype) (Ψ.symm y)
    refine ⟨z.1, ?_, ?_, ?_⟩
    · exact (isCocycleOn_iff_mem_Z1 (SSGRoute.res k K) z.1).mpr z.2.1
    · exact Work.SSGRoute.top_isLocConstOn_of_isLocallyConstant z.2.2
    · rw [hβ_eq z]
      have hz' : Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E z = Ψ.symm y := hz
      rw [hz', AddEquiv.apply_symm_apply]

end Work.SSGRoute

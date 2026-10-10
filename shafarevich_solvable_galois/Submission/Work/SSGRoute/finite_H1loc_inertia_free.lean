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
import Submission.Work.SSGRoute.finite_openKernel_homs_inertia_kernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Classical

noncomputable section

/-!
# Finiteness of the local `H¹` of the inertia subgroup (residue characteristic ≠ `p`)

This file proves `Work.SSGRoute.finite_H1loc_inertia_free`: the locally constant cohomology
`H1loc p k Ω K M I` of the inertia subgroup `I = inertiaSub k Ω A` of a finite place `A` with
residue characteristic different from `p`, with coefficients in a finite `𝔽_p[Gal(K/k)]`-module
`M`, is finite.

The mathematical content splits in two:

* **group theory** (this file): a locally constant `1`-cocycle of `I` with values in `M` is
  determined by its restriction to the kernel `I ⊓ G_K` (which acts trivially on `M` and on which
  the cocycle is therefore a group homomorphism) together with its values on a set of coset
  representatives of `I ⊓ G_K` in `I`; this reduces finiteness of the cocycles to finiteness of
  the open-kernel homomorphisms `I ⊓ G_K →* M`.  This is the exact analogue of
  `Work.SSGRoute.finite_Z1_decomp` for the decomposition group.

* **arithmetic** (`Work.SSGRoute.finite_openKernel_homs_inertia_kernel`, proved elsewhere): the
  open-kernel homomorphisms `I ⊓ G_K →* M` form a finite set.
-/

section GeneralCocycles

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The canonical action of a subgroup `H ≤ G_k` on a `Gal(K/k)`-module**, through the
restriction `res k K : G_k →* Gal(K/k)`.  This is `Work.SSGRoute.decompDistribMulAction`
generalised from the decomposition group to an arbitrary subgroup. -/
@[instance_reducible] def subgroupDistribMulAction (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [DistribMulAction (K ≃ₐ[k] K) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : DistribMulAction ↥H M where
  smul h m := SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m
  one_smul m := by
    show SSGRoute.res k K (((1 : ↥H) : Ω ≃ₐ[k] Ω)) • m = m
    rw [show ((1 : ↥H) : Ω ≃ₐ[k] Ω) = 1 from rfl, map_one, one_smul]
  mul_smul h1 h2 m := by
    show SSGRoute.res k K (((h1 * h2 : ↥H) : Ω ≃ₐ[k] Ω)) • m
      = SSGRoute.res k K ((h1 : Ω ≃ₐ[k] Ω)) • (SSGRoute.res k K ((h2 : Ω ≃ₐ[k] Ω)) • m)
    rw [show ((h1 * h2 : ↥H) : Ω ≃ₐ[k] Ω) = (h1 : Ω ≃ₐ[k] Ω) * (h2 : Ω ≃ₐ[k] Ω) from rfl,
      map_mul, mul_smul]
  smul_zero h := smul_zero _
  smul_add h m n := smul_add _ _ _

/-- **The reduction.**  For a subgroup `H ≤ G_k` such that `U = H ⊓ G_K` acts trivially on the
`𝔽_p`-module `M`, finiteness of the open-kernel homomorphisms `U →* Multiplicative M` forces
finiteness of the locally constant `1`-cocycles `Z¹_c(H, M)`.

The proof is that of `Work.SSGRoute.finite_Z1_decomp`, with the decomposition group replaced by an
arbitrary subgroup `H`: the restriction of a cocycle to `U` is a homomorphism (because `U` acts
trivially on `M`) and its values on a set-theoretic section `s` of the restriction
`res k K : H →* Gal(K/k)` together determine the cocycle, since `x = s (res x) · ((s (res x))⁻¹ x)`
and the action of `H` on `M` factors through `res k K`. -/
theorem finite_Z1_of_finite_homs
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    [DistribMulAction ↥H M]
    (htriv : ∀ (u : ↥(H ⊓ K.fixingSubgroup)) (m : M),
      (Subgroup.inclusion inf_le_left u : ↥H) • m = m)
    (h : Finite {χ : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(H ⊓ K.fixingSubgroup))}) :
    Finite ↥(Work.AbsoluteKummer.Z1 ↥H M) := by
  -- the arithmetic input
  have hcore : Finite {χ : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(H ⊓ K.fixingSubgroup))} := h
  -- the finite quotient of `H` by `H ⊓ G_K`
  have hQmem : ∀ q ∈ H.map (SSGRoute.res k K),
      ∃ σ : ↥H, SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) = q := by
    intro q hq
    rcases Subgroup.mem_map.mp hq with ⟨σ, hσ, hσq⟩
    exact ⟨⟨σ, hσ⟩, hσq⟩
  let s : (K ≃ₐ[k] K) → ↥H := fun q =>
    if h : q ∈ H.map (SSGRoute.res k K) then Classical.choose (hQmem q h) else 1
  have hs : ∀ q (h : q ∈ H.map (SSGRoute.res k K)),
      SSGRoute.res k K (s q : Ω ≃ₐ[k] Ω) = q := by
    intro q h
    simp only [s]
    rw [dif_pos h]
    exact Classical.choose_spec (hQmem q h)
  -- `f 1 = 0` for a crossed homomorphism
  have hzero : ∀ f : ↥(Work.AbsoluteKummer.Z1 ↥H M),
      f.1 (1 : ↥H) = 0 := by
    intro f
    have h := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥H) (M := M) f.1).mp f.2 |>.1
    have h11 : f.1 (1 : ↥H) = f.1 (1 : ↥H) + f.1 (1 : ↥H) := by
      simpa using h 1 1
    have h3 : f.1 (1 : ↥H) + f.1 (1 : ↥H) = f.1 (1 : ↥H) + 0 := by
      rw [add_zero]
      exact h11.symm
    exact add_left_cancel h3
  -- the homomorphism induced on the kernel
  let χfun : ↥(Work.AbsoluteKummer.Z1 ↥H M) →
      (↥(H ⊓ K.fixingSubgroup) →* Multiplicative M) := fun f =>
    { toFun := fun u => Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left u))
      map_one' := by
        show Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left
          (1 : ↥(H ⊓ K.fixingSubgroup)))) = Multiplicative.ofAdd (0 : M)
        rw [show (Subgroup.inclusion inf_le_left
          (1 : ↥(H ⊓ K.fixingSubgroup)) : ↥H) = 1 from map_one _]
        rw [hzero f]
      map_mul' := by
        intro a b
        have h := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥H) (M := M) f.1).mp f.2 |>.1
        have h1 := h (Subgroup.inclusion inf_le_left a) (Subgroup.inclusion inf_le_left b)
        show Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left (a * b))) =
          Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left a) +
            f.1 (Subgroup.inclusion inf_le_left b))
        rw [show (Subgroup.inclusion inf_le_left (a * b) : ↥H) =
            Subgroup.inclusion inf_le_left a * Subgroup.inclusion inf_le_left b from map_mul _ a b]
        rw [h1, htriv a (f.1 (Subgroup.inclusion inf_le_left b)), add_comm] }
  -- the kernel of that homomorphism is open
  have hker_open : ∀ f : ↥(Work.AbsoluteKummer.Z1 ↥H M),
      IsOpen ((χfun f).ker : Set ↥(H ⊓ K.fixingSubgroup)) := by
    intro f
    have hlc := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥H) (M := M) f.1).mp f.2 |>.2
    obtain ⟨V, hVopen, h1V, hV⟩ := hlc (1 : ↥H)
    obtain ⟨W, hWopen, hWV⟩ := isOpen_induced_iff.mp hVopen
    have h1W : (1 : Ω ≃ₐ[k] Ω) ∈ W := by
      have h : (1 : ↥H) ∈ (Subtype.val : ↥H → Ω ≃ₐ[k] Ω) ⁻¹' W := by
        rw [hWV]
        exact h1V
      exact h
    refine Subgroup.isOpen_of_mem_nhds (χfun f).ker (g := 1) ?_
    have hWopen' : IsOpen
        ((fun u : ↥(H ⊓ K.fixingSubgroup) => (u : Ω ≃ₐ[k] Ω)) ⁻¹' W) :=
      hWopen.preimage continuous_subtype_val
    have h1W' : (1 : ↥(H ⊓ K.fixingSubgroup)) ∈
        (fun u : ↥(H ⊓ K.fixingSubgroup) => (u : Ω ≃ₐ[k] Ω)) ⁻¹' W := by
      simp only [Set.mem_preimage, Subgroup.coe_one]
      exact h1W
    refine Filter.mem_of_superset (IsOpen.mem_nhds hWopen' h1W') ?_
    intro u hu
    simp only [Set.mem_preimage] at hu
    have huin : (Subgroup.inclusion inf_le_left u : ↥H) ∈
        (Subtype.val : ↥H → Ω ≃ₐ[k] Ω) ⁻¹' W := by
      simp only [Set.mem_preimage]
      rwa [Subgroup.coe_inclusion]
    have hVmem : (Subgroup.inclusion inf_le_left u : ↥H) ∈ V := by
      rw [← hWV]
      exact huin
    show Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left u)) = 1
    rw [hV _ hVmem, hzero f]
    rfl
  -- the key injectivity statement
  have hkey : ∀ f g : ↥(Work.AbsoluteKummer.Z1 ↥H M), χfun f = χfun g →
      (∀ q : K ≃ₐ[k] K, f.1 (s q) = g.1 (s q)) → f = g := by
    intro f g hχ hval
    apply Subtype.ext
    funext x
    have hχu : ∀ u : ↥(H ⊓ K.fixingSubgroup),
        f.1 (Subgroup.inclusion inf_le_left u) = g.1 (Subgroup.inclusion inf_le_left u) := by
      intro u
      have h' : Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left u)) =
          Multiplicative.ofAdd (g.1 (Subgroup.inclusion inf_le_left u)) :=
        congrFun (congrArg DFunLike.coe hχ) u
      exact Multiplicative.ofAdd.injective h'
    have hq : SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) ∈ H.map (SSGRoute.res k K) :=
      ⟨(x : Ω ≃ₐ[k] Ω), x.2, rfl⟩
    have hmemU : ((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) : ↥H) :
        Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω) ∈ H ⊓ K.fixingSubgroup := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact H.mul_mem (H.inv_mem (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))).2) x.2
      · have hres : SSGRoute.res k K (((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) :
            ↥H) : Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω)) = 1 := by
          rw [map_mul, map_inv, hs _ hq]
          exact inv_mul_cancel _
        have hle : (SSGRoute.res k K).ker ≤ (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) := by
          rw [IntermediateField.restrictNormalHom_ker (E := K)]
        simpa using hle (MonoidHom.mem_ker.mpr hres)
    let u : ↥(H ⊓ K.fixingSubgroup) :=
      ⟨((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) : ↥H) : Ω ≃ₐ[k] Ω)⁻¹ *
        (x : Ω ≃ₐ[k] Ω), hmemU⟩
    have hxu : s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) * (Subgroup.inclusion inf_le_left u) = x := by
      apply Subtype.ext
      show ((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) : ↥H) : Ω ≃ₐ[k] Ω) *
        ((Subgroup.inclusion inf_le_left u : ↥H) : Ω ≃ₐ[k] Ω) = (x : Ω ≃ₐ[k] Ω)
      rw [Subgroup.coe_inclusion]
      exact mul_inv_cancel_left _ _
    have hcrossf := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥H) (M := M) f.1).mp f.2 |>.1
    have hcrossg := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥H) (M := M) g.1).mp g.2 |>.1
    calc f.1 x = f.1 (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) * (Subgroup.inclusion inf_le_left u)) :=
          by rw [hxu]
      _ = (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) • f.1 (Subgroup.inclusion inf_le_left u) +
            f.1 (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) := hcrossf _ _
      _ = (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) • g.1 (Subgroup.inclusion inf_le_left u) +
            g.1 (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) := by rw [hχu u, hval _]
      _ = g.1 (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) * (Subgroup.inclusion inf_le_left u)) :=
          (hcrossg _ _).symm
      _ = g.1 x := by rw [hxu]
  -- the injection into a finite target
  let Φ : ↥(Work.AbsoluteKummer.Z1 ↥H M) →
      ({χ : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M //
        IsOpen (χ.ker : Set ↥(H ⊓ K.fixingSubgroup))} ×
        ((K ≃ₐ[k] K) → M)) :=
    fun f => (⟨χfun f, hker_open f⟩, fun q => f.1 (s q))
  have hΦinj : Function.Injective Φ := by
    intro f g hfg
    refine hkey f g ?_ ?_
    · exact congrArg (fun z => (z.1 : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M)) hfg
    · intro q
      exact congrFun (congrArg (fun z => z.2) hfg) q
  haveI : Finite {χ : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(H ⊓ K.fixingSubgroup))} := hcore
  haveI : Finite (K ≃ₐ[k] K) := inferInstance
  haveI : Finite ((K ≃ₐ[k] K) → M) := inferInstance
  exact Finite.of_injective Φ hΦinj

end GeneralCocycles


/-! ## The target theorem -/

/-- **Finiteness of the local `H¹` of the inertia subgroup (residue characteristic ≠ `p`).** -/
theorem finite_H1loc_inertia_free
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Finite (Work.SSGRoute.H1loc p k Ω K M (Work.SSGRoute.inertiaSub k Ω A)) := by
  intro M _ _ _ _ _
  letI : DistribMulAction ↥(SSGRoute.inertiaSub k Ω A) M :=
    subgroupDistribMulAction k Ω K M (SSGRoute.inertiaSub k Ω A)
  have htriv : ∀ (u : ↥(SSGRoute.inertiaSub k Ω A ⊓ K.fixingSubgroup)) (m : M),
      (Subgroup.inclusion inf_le_left u : ↥(SSGRoute.inertiaSub k Ω A)) • m = m := by
    intro u m
    have hker : SSGRoute.res k K
        ((Subgroup.inclusion inf_le_left u : ↥(SSGRoute.inertiaSub k Ω A)) : Ω ≃ₐ[k] Ω) = 1 := by
      have hle : (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) ≤ (SSGRoute.res k K).ker := by
        rw [IntermediateField.restrictNormalHom_ker (E := K)]
      exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_inf.mp u.2).2)
    show SSGRoute.res k K
      ((Subgroup.inclusion inf_le_left u : ↥(SSGRoute.inertiaSub k Ω A)) : Ω ≃ₐ[k] Ω) • m = m
    rw [hker, one_smul]
  haveI hZ1 : Finite ↥(Work.AbsoluteKummer.Z1 ↥(SSGRoute.inertiaSub k Ω A) M) :=
    finite_Z1_of_finite_homs p k Ω K (SSGRoute.inertiaSub k Ω A) M htriv
      (finite_openKernel_homs_inertia_kernel p k Ω K A hA h M)
  haveI hH1 : Finite (Work.AbsoluteKummer.H1 ↥(SSGRoute.inertiaSub k Ω A) M) :=
    Finite.of_surjective (Work.AbsoluteKummer.H1π ↥(SSGRoute.inertiaSub k Ω A) M)
      (QuotientAddGroup.mk'_surjective _)
  exact Finite.of_injective
    (H1locEquivH1 p k Ω K M (SSGRoute.inertiaSub k Ω A) (fun _ _ => rfl))
    (H1locEquivH1 p k Ω K M (SSGRoute.inertiaSub k Ω A) (fun _ _ => rfl)).injective

end

end Work.SSGRoute

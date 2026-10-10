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
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.InfInertiaClosureDefs
import Submission.Work.SSGRoute.exists_frobenius_complement
import Submission.Work.SSGRoute.exists_isFrobLift
import Submission.Work.SSGRoute.exists_level_inertiaDeg_mul_dvd
import Submission.Work.SSGRoute.index_dvd_of_zpowers_generates
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
import Submission.Work.SSGRoute.restrictNormalHom_mem_zpowers_of_mem_topologicalClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Frobenius complement of the inertia subgroup has infinite order

For a finite place `A` of an algebraic closure `Ω` of a number field `k`, the inertia subgroup
`I_A = Work.SSGRoute.inertiaSub k Ω A` has a procyclic complement in the decomposition group
`D_A = SSGRoute.decomp k A` generated by an element `σ` of infinite order:

`D_A ≤ I_A ⊔ closure (zpowers σ)` and `I_A ⊓ closure (zpowers σ) = ⊥`.

## The proof

`σ` is a Frobenius lift at `A`, i.e. an element whose class generates `D_A ⧸ (D_A ⊓ V)` for every
open `V ≤ Ĝ = Ω ≃ₐ[k] Ω` containing `I_A` (`Work.SSGRoute.IsFrobLift`); such an element exists by
`Work.SSGRoute.exists_isFrobLift`.  From this predicate:

* `D_A ≤ I_A ⊔ closure (zpowers σ)` is `Work.SSGRoute.decomp_le_inertia_sup_closure`
  (`Submission/Work/SSGRoute/exists_frobenius_complement.lean`);
* `I_A ⊓ closure (zpowers σ) = ⊥` is proved *here* as `inf_inertiaSub_inf_closure_eq_bot`: for a
  finite normal level `L ⊆ Ω` the group `Ideal.inertia Gal(L/k) P_L` is normal in the stabiliser
  `D_L` of the prime `P_L` of `𝓞 L` below `A`; `D_L ⧸ I_L ≅ Gal(κ_L/κ_k)` is cyclic of order the
  inertia degree `f_L = inertiaDeg P_L`, generated by the image of `σ`, so an element `γ` of
  `closure (zpowers σ)` whose restriction to `L` lies in `I_L` has restriction on every sublevel
  `M ⊆ L` that is killed by `f_L · d` for any `d` with `(σ|_M) ^ d = 1` and `d ∣ f_L`; taking `M`
  a level at which `γ` acts non-trivially and `L` a level above it whose inertia degree is
  divisible by the order `d` of `σ|_M` (`Work.SSGRoute.exists_level_inertiaDeg_mul_dvd`) forces
  `γ|_M = 1`, a contradiction.  The restriction of `γ` to `L` is a power of `σ|_L` by
  `Work.SSGRoute.restrictNormalHom_mem_zpowers_of_mem_topologicalClosure`;
* `σ` has infinite order: if `σ ^ n = 1` then the index of every level subgroup
  `Work.SSGRoute.levelSub A M` in `D_A` divides `n` (`Work.SSGRoute.index_dvd_of_zpowers_generates`,
  using generation modulo the level subgroup and the dictionary
  `Work.SSGRoute.levelSub_comap_index_eq_inertiaDeg`), while levels whose index exceeds `n` exist by
  `Work.SSGRoute.exists_level_inertiaDeg_mul_dvd`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open scoped Pointwise

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- `frobV A L = I_A ⊔ G_L` is open in the Krull profile: it contains the open fixing subgroup
`G_L` of the finite level `L`. -/
theorem frobV_isOpen_free (A : ValuationSubring Ω) (i : FrobIndex k Ω) :
    IsOpen (frobV A i : Set (Ω ≃ₐ[k] Ω)) := by
  haveI := i.2.1
  exact Subgroup.isOpen_mono le_sup_right (IntermediateField.fixingSubgroup_isOpen i.1)

/-- **The elements of `D_A ⊓ (I_A ⊔ G_L)` act trivially on the level ring** `A ∩ L` modulo its
maximal ideal: writing such an element as `i * g` with `i ∈ I_A` and `g` fixing the level `L`
pointwise, the `g`-part fixes `L` and the `i`-part is an inertia element. -/
theorem frobK_le_levelSub (A : ValuationSubring Ω) (M : IntermediateField k Ω)
    [FiniteDimensional k M] [Normal k M] :
    frobK A ⟨M, ‹FiniteDimensional k M›, ‹Normal k M›⟩ ≤
      (Work.SSGRoute.levelSub A M).subgroupOf (SSGRoute.decomp k A) := by
  intro δ hδ
  change (δ : Ω ≃ₐ[k] Ω) ∈ frobV A ⟨M, ‹FiniteDimensional k M›, ‹Normal k M›⟩ at hδ
  change (δ : Ω ≃ₐ[k] Ω) ∈ Work.SSGRoute.levelSub A M
  haveI : (M.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal :=
    IsGalois.fixingSubgroup_normal_of_isGalois M
  have hδ' : (δ : Ω ≃ₐ[k] Ω) ∈
      (((inertiaSub k Ω A ⊔ M.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
        Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := hδ
  rw [Subgroup.mul_normal (inertiaSub k Ω A) M.fixingSubgroup, Set.mem_mul] at hδ'
  obtain ⟨i, hi, g, hg, hig⟩ := hδ'
  refine ⟨δ.2, fun x => ?_⟩
  have hxΩ : ((x : ↥M) : Ω) ∈ M := (x : ↥M).2
  have hxB : ((x : ↥M) : Ω) ∈ A := by
    have h := (ValuationSubring.mem_comap).mp x.2
    simpa [IntermediateField.algebraMap_apply] using h
  have hgfix : g ((x : ↥M) : Ω) = ((x : ↥M) : Ω) :=
    (IntermediateField.mem_fixingSubgroup_iff M g).mp hg ((x : ↥M) : Ω) hxΩ
  rw [← hig, AlgEquiv.mul_apply, hgfix]
  exact ((Work.SSGRoute.mem_inertiaSub k Ω A i).mp hi).2 _ hxB

/-- **A function form of `IsFrobLift`**: for a Frobenius lift `σ` at `A`, the quotient of `D_A` by
the level subgroup `Work.SSGRoute.levelSub A M` of a finite normal level `M` is generated by the
class of `σ`. -/
theorem frobK_zpowers_generates_levelSub (A : ValuationSubring Ω) (M : IntermediateField k Ω)
    [FiniteDimensional k M] [Normal k M] (σ : Ω ≃ₐ[k] Ω) (hσ : IsFrobLift k A σ) :
    ∀ δ : ↥(SSGRoute.decomp k A), ∃ m : ℤ,
      δ⁻¹ * (⟨σ, hσ.1⟩ : ↥(SSGRoute.decomp k A)) ^ m ∈
        (Work.SSGRoute.levelSub A M).subgroupOf (SSGRoute.decomp k A) := by
  intro δ
  obtain ⟨m, hm⟩ := hσ.2 (frobV A ⟨M, ‹FiniteDimensional k M›, ‹Normal k M›⟩)
    (frobV_isOpen_free A ⟨M, ‹FiniteDimensional k M›, ‹Normal k M›⟩) le_sup_left
    (δ : Ω ≃ₐ[k] Ω) δ.2
  refine ⟨m, frobK_le_levelSub A M ?_⟩
  change ((δ⁻¹ * (⟨σ, hσ.1⟩ : ↥(SSGRoute.decomp k A)) ^ m : ↥(SSGRoute.decomp k A)) :
    Ω ≃ₐ[k] Ω) ∈ frobV A ⟨M, ‹FiniteDimensional k M›, ‹Normal k M›⟩
  simpa using hm

/-- **The order of the level quotient divides the exponent of `σ`**: if `σ ^ n = 1` then the index
of every level subgroup `Work.SSGRoute.levelSub A M` divides `n`. -/
theorem levelSub_index_dvd_of_pow_eq_one (A : ValuationSubring Ω)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M]
    (σ : Ω ≃ₐ[k] Ω) (hσ : IsFrobLift k A σ) (n : ℕ) (hn : σ ^ n = 1) :
    ((Work.SSGRoute.levelSub A M).comap (Subgroup.subtype (SSGRoute.decomp k A))).index ∣ n := by
  have hn' : (⟨σ, hσ.1⟩ : ↥(SSGRoute.decomp k A)) ^ n = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    simpa using hn
  exact index_dvd_of_zpowers_generates
    ((Work.SSGRoute.levelSub A M).comap (Subgroup.subtype (SSGRoute.decomp k A)))
    ⟨σ, hσ.1⟩ n (frobK_zpowers_generates_levelSub A M σ hσ) hn'

/-- **The level decomposition group is generated by the image of the Frobenius lift modulo the
level inertia.**  For a finite normal level `L` and `x` in the stabiliser `D_L` of the prime of
`𝓞 L` below `A` there is `m : ℤ` with `x⁻¹ (σ|_L)^m ∈ I_L`.

Proof: lift `x` to some `δ ∈ D_A` using `Work.SSGRoute.range_restrictNormalHom_eq_stabilizer`,
apply `IsFrobLift` with the open subgroup `frobV A L = I_A ⊔ G_L`, split `δ⁻¹σ^m = i · g` with
`i ∈ I_A` and `g` fixing `L` pointwise (possible since `G_L` is normal in `G_k`), and note that
`x⁻¹ (σ|_L)^m = (δ⁻¹σ^m)|_L = i|_L ∈ I_L` because the image of `I_A` in `Gal(L/k)` is the level
inertia (`Work.SSGRoute.inertiaSub_image_eq_levelInertia`). -/
theorem levelDecomp_zpowers_generates (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (σ : Ω ≃ₐ[k] Ω) (hσ : IsFrobLift k A σ)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] [NumberField ↥L]
    (hσbar : AlgEquiv.restrictNormalHom L σ ∈ Work.SSGRoute.levelDecompAt k Ω A hA L) :
    ∀ x : Work.SSGRoute.levelDecompAt k Ω A hA L, ∃ m : ℤ,
      x⁻¹ * (⟨AlgEquiv.restrictNormalHom L σ, hσbar⟩ : Work.SSGRoute.levelDecompAt k Ω A hA L) ^ m ∈
        Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L := by
  intro x
  have hxr : (x : ↥L ≃ₐ[k] ↥L) ∈
      ((AlgEquiv.restrictNormalHom L).comp (Subgroup.subtype (SSGRoute.decomp k A))).range := by
    rw [Work.SSGRoute.range_restrictNormalHom_eq_stabilizer A hA L]
    exact x.2
  obtain ⟨δ, hδ⟩ := MonoidHom.mem_range.mp hxr
  obtain ⟨m, hm⟩ := hσ.2 (frobV A ⟨L, ‹FiniteDimensional k L›, ‹Normal k L›⟩)
    (frobV_isOpen_free A ⟨L, ‹FiniteDimensional k L›, ‹Normal k L›⟩)
    le_sup_left (δ : Ω ≃ₐ[k] Ω) δ.2
  refine ⟨m, ?_⟩
  haveI : (L.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal :=
    IsGalois.fixingSubgroup_normal_of_isGalois L
  have hm' : (δ : Ω ≃ₐ[k] Ω)⁻¹ * σ ^ m ∈
      (((inertiaSub k Ω A ⊔ L.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
        Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := hm
  rw [Subgroup.mul_normal (inertiaSub k Ω A) L.fixingSubgroup, Set.mem_mul] at hm'
  obtain ⟨i, hi, g, hg, hig⟩ := hm'
  have hgL : AlgEquiv.restrictNormalHom L g = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hg
  have hδ' : AlgEquiv.restrictNormalHom L (δ : Ω ≃ₐ[k] Ω) = (x : ↥L ≃ₐ[k] ↥L) := hδ
  have hkey : AlgEquiv.restrictNormalHom L i =
      (x : ↥L ≃ₐ[k] ↥L)⁻¹ * (AlgEquiv.restrictNormalHom L σ) ^ m := by
    have h2 := congrArg (AlgEquiv.restrictNormalHom L) hig
    simp only [map_mul, map_inv, map_zpow] at h2
    rw [hgL, mul_one, hδ'] at h2
    exact h2
  have hmemI : AlgEquiv.restrictNormalHom L i ∈ Work.SSGRoute.levelInertiaOf k Ω A hA L := by
    rw [← Work.SSGRoute.inertiaSub_image_eq_levelInertia k Ω A hA L]
    exact Subgroup.mem_map_of_mem _ hi
  rw [Work.SSGRoute.levelInertiaInDecompAt_eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
  rw [← hkey]
  exact hmemI

/-- **The class of the Frobenius lift generates the level quotient,** hence has order the inertia
degree `f_L = [κ_L : κ_k] = inertiaDeg P_L` of the level prime.  The quotient
`D_L ⧸ I_L` is finite (`Nat.card = (I_L).relIndex D_L`, which is the inertia degree by
`Work.SSGRoute.inertia_relIndex_stabilizer_eq_inertiaDeg`) and cyclic, generated by the class of
`σ|_L` by `levelDecomp_zpowers_generates`; the order of a generator of a finite cyclic group is the
cardinality of the group (`orderOf_eq_card_of_forall_mem_zpowers`). -/
theorem levelQuotient_orderOf_eq_inertiaDeg (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (σ : Ω ≃ₐ[k] Ω) (hσ : IsFrobLift k A σ)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] [NumberField ↥L]
    (hσbar : AlgEquiv.restrictNormalHom L σ ∈ Work.SSGRoute.levelDecompAt k Ω A hA L) :
    orderOf (QuotientGroup.mk' (Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L)
        (⟨AlgEquiv.restrictNormalHom L σ, hσbar⟩ : Work.SSGRoute.levelDecompAt k Ω A hA L)) =
      (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
  have hgen := levelDecomp_zpowers_generates A hA σ hσ L hσbar
  have htop : Subgroup.zpowers (QuotientGroup.mk' (Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L)
      (⟨AlgEquiv.restrictNormalHom L σ, hσbar⟩ : Work.SSGRoute.levelDecompAt k Ω A hA L)) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L) y
    obtain ⟨m, hm⟩ := hgen x
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    have h2 : QuotientGroup.mk' (Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L)
        (x⁻¹ * (⟨AlgEquiv.restrictNormalHom L σ, hσbar⟩ : Work.SSGRoute.levelDecompAt k Ω A hA L) ^ m)
        = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    have h3 : (QuotientGroup.mk' (Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L) x)⁻¹ *
        (QuotientGroup.mk' (Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L)
          (⟨AlgEquiv.restrictNormalHom L σ, hσbar⟩ : Work.SSGRoute.levelDecompAt k Ω A hA L)) ^ m
        = 1 := by
      simpa using h2
    exact (inv_mul_eq_one.mp h3).symm
  have hcard : Nat.card (Work.SSGRoute.levelDecompAt k Ω A hA L ⧸
      Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L) =
      (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    rw [← Subgroup.index_eq_card]
    rw [Work.SSGRoute.levelInertiaInDecompAt_eq]
    exact Work.SSGRoute.inertia_relIndex_stabilizer_eq_inertiaDeg A hA L
  rw [orderOf_eq_card_of_forall_mem_zpowers (fun x => by rw [htop]; exact Subgroup.mem_top x)]
  exact hcard

/-- **The inertia subgroup meets the closed cyclic subgroup generated by a Frobenius lift
trivially.**

Let `σ` be a Frobenius lift at `A` (`IsFrobLift`), `D = D_A`, `I = I_A` and
`C = closure (zpowers σ)`.  Then `I ⊓ C = ⊥`.

Proof.  Let `γ ∈ I ⊓ C` and suppose `γ ≠ 1`.  Choose a finite normal level `M ⊆ Ω`
(`FiniteDimensional`, `Normal`, `NumberField`) with `γ ∉ M.fixingSubgroup`: if `γ x ≠ x`, take `M`
the normal closure of `k(x)`.  Let `d = orderOf (σ|_M)`, so `(σ|_M)^d = 1`.  By
`Work.SSGRoute.exists_level_inertiaDeg_mul_dvd` there is a finite normal level `L ⊇ M` with
`(d · f_M) ∣ f_L`, where `f` denotes the inertia degree of the level prime; in particular
`d ∣ f_L`.

Now `γ|_L` is a power of `σ|_L` (`restrictNormalHom_mem_zpowers_of_mem_topologicalClosure`),
say `γ|_L = (σ|_L)^m`, and `γ|_L ∈ I_L` (image of `I_A`, `inertiaSub_image_eq_levelInertia`).
By `levelQuotient_orderOf_eq_inertiaDeg` the class of `σ|_L` in `D_L ⧸ I_L` has order `f_L`, so
`f_L ∣ m`.  Finally, since `f_L` is a multiple of `d` and `(σ|_M)^d = 1`, the restriction of
`(σ|_L)^m` to `M` is `(σ|_M)^m = (σ|_M)^{f_L · k} = 1`, whence `γ|_M = 1`, i.e.
`γ ∈ M.fixingSubgroup` — contradicting the choice of `M`. -/
theorem inf_inertiaSub_inf_closure_eq_bot
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (σ : Ω ≃ₐ[k] Ω) (hσ : IsFrobLift k A σ) :
    Work.SSGRoute.inertiaSub k Ω A ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro γ hγ
  obtain ⟨hγI, hγC⟩ := hγ
  by_contra hγ1
  -- ## Step 1: a finite normal level `M` at which `γ` acts non-trivially
  have hx : ∃ x : Ω, γ x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hγ1 (AlgEquiv.ext hcon)
  obtain ⟨x0, hx0⟩ := hx
  let L0 : IntermediateField k Ω := IntermediateField.adjoin k ({x0} : Set Ω)
  haveI : FiniteDimensional k L0 :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x0).isIntegral
  let M : IntermediateField k Ω := IntermediateField.normalClosure k L0 Ω
  haveI hMfd : FiniteDimensional k M := normalClosure.is_finiteDimensional k L0 Ω
  haveI hMnorm : Normal k M := inferInstance
  haveI hMnf : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField M
  have hx0M : x0 ∈ M := IntermediateField.le_normalClosure L0
    (IntermediateField.subset_adjoin k _ (Set.mem_singleton x0))
  have hγM : γ ∉ M.fixingSubgroup := fun hmem =>
    hx0 ((IntermediateField.mem_fixingSubgroup_iff M γ).mp hmem x0 hx0M)
  -- ## Step 2: the order `d` of `σ` on the level `M`
  haveI hMfin : Fintype (↥M ≃ₐ[k] ↥M) := AlgEquiv.fintype k ↥M
  haveI : Finite (↥M ≃ₐ[k] ↥M) := Finite.of_fintype _
  set d : ℕ := orderOf (AlgEquiv.restrictNormalHom M σ) with hddef
  have hdne : d ≠ 0 := by
    rw [hddef, ← Nat.card_zpowers (AlgEquiv.restrictNormalHom M σ)]
    exact Nat.card_ne_zero.mpr ⟨Nonempty.intro ⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  -- ## Step 3: a level `L ⊇ M` whose inertia degree is divisible by `d`
  obtain ⟨L, hLfd, hLnorm, hLnf, hMle, hdvd⟩ :=
    Work.SSGRoute.exists_level_inertiaDeg_mul_dvd k Ω A hA M d hdne
  haveI := hLfd
  haveI := hLnorm
  haveI := hLnf
  have hdfL : d ∣ (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) := dvd_trans (dvd_mul_right d _) hdvd
  -- ## Step 4: the restriction of `γ` to `L` is a power of the restriction of `σ`
  have hmem1 : AlgEquiv.restrictNormalHom L γ ∈
      Subgroup.zpowers (AlgEquiv.restrictNormalHom L σ) :=
    Work.SSGRoute.restrictNormalHom_mem_zpowers_of_mem_topologicalClosure k Ω L σ γ hγC
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem1
  -- ## Step 5: the two restrictions lie in the level decomposition group, `γ` even in the inertia
  have hσbarD : AlgEquiv.restrictNormalHom L σ ∈ Work.SSGRoute.levelDecompAt k Ω A hA L := by
    have h : AlgEquiv.restrictNormalHom L σ ∈
        ((AlgEquiv.restrictNormalHom L).comp (Subgroup.subtype (SSGRoute.decomp k A))).range :=
      ⟨⟨σ, hσ.1⟩, rfl⟩
    rwa [Work.SSGRoute.range_restrictNormalHom_eq_stabilizer A hA L] at h
  have hγbarD : AlgEquiv.restrictNormalHom L γ ∈ Work.SSGRoute.levelDecompAt k Ω A hA L := by
    have h : AlgEquiv.restrictNormalHom L γ ∈
        ((AlgEquiv.restrictNormalHom L).comp (Subgroup.subtype (SSGRoute.decomp k A))).range :=
      ⟨⟨γ, hγI.1⟩, rfl⟩
    rwa [Work.SSGRoute.range_restrictNormalHom_eq_stabilizer A hA L] at h
  have hγbarI : AlgEquiv.restrictNormalHom L γ ∈ Work.SSGRoute.levelInertiaOf k Ω A hA L := by
    rw [← Work.SSGRoute.inertiaSub_image_eq_levelInertia k Ω A hA L]
    exact Subgroup.mem_map_of_mem _ hγI
  -- ## Step 6: the class of `σ` in the level quotient has order the inertia degree
  have horder := levelQuotient_orderOf_eq_inertiaDeg A hA σ hσ L hσbarD
  -- ## Step 7: hence the inertia degree divides `m`
  have hfLm : (((Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) : ℕ) : ℤ) ∣ m := by
    rw [← horder]
    refine orderOf_dvd_iff_zpow_eq_one.mpr ?_
    have hqγ : QuotientGroup.mk' (Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L)
        (⟨AlgEquiv.restrictNormalHom L γ, hγbarD⟩ : Work.SSGRoute.levelDecompAt k Ω A hA L) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Work.SSGRoute.levelInertiaInDecompAt_eq,
        Subgroup.mem_subgroupOf]
      exact hγbarI
    have h3 : (QuotientGroup.mk' (Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L)
        (⟨AlgEquiv.restrictNormalHom L σ, hσbarD⟩ : Work.SSGRoute.levelDecompAt k Ω A hA L)) ^ m
        = QuotientGroup.mk' (Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L)
          (⟨AlgEquiv.restrictNormalHom L γ, hγbarD⟩ : Work.SSGRoute.levelDecompAt k Ω A hA L) := by
      rw [(map_zpow _ _ _).symm]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hm
    rw [h3, hqγ]
  -- ## Step 8: `(σ|_M) ^ m = 1`
  have hσMd : (AlgEquiv.restrictNormalHom M σ) ^ d = 1 := by
    rw [hddef]; exact pow_orderOf_eq_one _
  have hσMm : (AlgEquiv.restrictNormalHom M σ) ^ m = 1 := by
    obtain ⟨t, ht⟩ := hfLm
    have hc : (((Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers k) : ℕ) : ℤ) =
        (d : ℤ) * ((((Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.inertiaDeg
          (NumberField.RingOfIntegers k)) / d : ℕ) : ℤ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdfL).symm
    rw [ht, hc, zpow_mul, zpow_mul]
    have h1 : (AlgEquiv.restrictNormalHom M σ) ^ (d : ℤ) = 1 := by
      rw [zpow_natCast, hddef, pow_orderOf_eq_one]
    rw [h1, one_zpow, one_zpow]
  -- ## Step 9: `γ` is trivial on `M`
  have hfix : ∀ z : ↥M, ((AlgEquiv.restrictNormalHom M γ) z : Ω) = z := by
    intro z
    calc ((AlgEquiv.restrictNormalHom M γ) z : Ω)
        = γ (z : Ω) := AlgEquiv.restrictNormalHom_apply M γ z
      _ = ((AlgEquiv.restrictNormalHom L γ) ⟨(z : Ω), hMle z.2⟩ : Ω) :=
            (AlgEquiv.restrictNormalHom_apply L γ ⟨(z : Ω), hMle z.2⟩).symm
      _ = (((AlgEquiv.restrictNormalHom L σ) ^ m) ⟨(z : Ω), hMle z.2⟩ : Ω) := by rw [hm]
      _ = ((AlgEquiv.restrictNormalHom L (σ ^ m)) ⟨(z : Ω), hMle z.2⟩ : Ω) := by
            rw [← map_zpow]
      _ = ((AlgEquiv.restrictNormalHom M (σ ^ m)) z : Ω) := by
            rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
      _ = (((AlgEquiv.restrictNormalHom M σ) ^ m) z : Ω) := by rw [← map_zpow]
      _ = ((1 : ↥M ≃ₐ[k] ↥M) z : Ω) := by rw [hσMm]
      _ = z := rfl
  refine hγM ?_
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  rw [← AlgEquiv.restrictNormalHom_apply M γ ⟨y, hy⟩]
  exact hfix ⟨y, hy⟩

theorem inertiaSub_frobenius_complement_inf_free
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A ∧
      (∀ n : ℕ, σ ^ n = 1 → n = 0) ∧
      SSGRoute.decomp k A ≤ Work.SSGRoute.inertiaSub k Ω A ⊔
        Subgroup.topologicalClosure (Subgroup.zpowers σ) ∧
      Work.SSGRoute.inertiaSub k Ω A ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥ := by
  obtain ⟨σ, hσ⟩ := Work.SSGRoute.exists_isFrobLift k Ω A hA
  have hsup := Work.SSGRoute.decomp_le_inertia_sup_closure k Ω A σ hσ
  have hinf := inf_inertiaSub_inf_closure_eq_bot A hA σ hσ
  refine ⟨σ, hσ.1, ?_, hsup, hinf⟩
  intro n hn
  by_contra hne
  have hnpos : 0 < n := Nat.pos_of_ne_zero hne
  -- a finite normal level whose inertia degree is larger than `n`
  haveI : FiniteDimensional k (⊥ : IntermediateField k Ω) := inferInstance
  haveI : Normal k (⊥ : IntermediateField k Ω) := inferInstance
  haveI : NumberField ↥(⊥ : IntermediateField k Ω) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (⊥ : IntermediateField k Ω)
  obtain ⟨M, hMfd, hMnorm, hMnf, -, hdvd⟩ :=
    Work.SSGRoute.exists_level_inertiaDeg_mul_dvd k Ω A hA (⊥ : IntermediateField k Ω)
      (n + 1) (by omega)
  haveI := hMfd
  haveI := hMnorm
  haveI := hMnf
  -- the index of the level subgroup is an inertia degree, hence divides `n`
  have hdvdn := levelSub_index_dvd_of_pow_eq_one A M σ hσ n hn
  have hidx := Work.SSGRoute.levelSub_comap_index_eq_inertiaDeg k Ω A hA M
  rw [hidx] at hdvdn
  have hle : (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) ≤ n := Nat.le_of_dvd hnpos hdvdn
  -- but that level has inertia degree at least `n + 1`
  have hbase : 0 < (Work.SSGRoute.levelPrime k Ω A hA (⊥ : IntermediateField k Ω)).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) :=
    Ideal.inertiaDeg_pos (Work.SSGRoute.levelPrime k Ω A hA (⊥ : IntermediateField k Ω)).asIdeal
      (NumberField.RingOfIntegers k)
  have hposM : 0 < (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) :=
    Ideal.inertiaDeg_pos (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal
      (NumberField.RingOfIntegers k)
  have h1 : (n + 1) *
      (Work.SSGRoute.levelPrime k Ω A hA (⊥ : IntermediateField k Ω)).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers k) ≤
      (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
    Nat.le_of_dvd hposM hdvd
  have h2 : n + 1 ≤ (n + 1) *
      (Work.SSGRoute.levelPrime k Ω A hA (⊥ : IntermediateField k Ω)).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers k) := by
    have h := Nat.mul_le_mul_left (n + 1) hbase
    simpa using h
  have hge : n + 1 ≤ (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) := le_trans h2 h1
  omega

end Work.SSGRoute

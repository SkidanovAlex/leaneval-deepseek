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
import Submission.Work.SSGRoute.exists_level_residueDeg
import Submission.Work.SSGRoute.kummer_character_realization_inf
import Submission.Work.SSGRoute.levelIndex
import Submission.Work.SSGRoute.localZhatHom_ker
import Submission.Work.SSGRoute.ramified_char_lift
import Submission.Work.SSGRoute.zhat_le_of_index
import Submission.Work.SSGRoute.zpowers_zhatGen_sup_powSubgroup

/-!
# The local structure of `D_A`: Frobenius generators and tame character lifting

This file proves `Work.SSGRoute.local_tame_lifting`, the local input of the Shafarevich route
(see `Submission/Work/SSGRoute/DESIGN.md`):

* **(a)** at every finite place `A` of `ℚ̄` over `ℚ`, the quotient `D_A/I_A` (inertia subgroup of
  the decomposition group) is pro-cyclic of rank one — generated by a Frobenius element `F` — and a
  continuous homomorphism from `D_A` to a finite group killing `I_A` is determined by its value on
  `F`;
* **(b)** a continuous totally ramified `ℤ/p^a`-valued character of `D_A` lifts to a totally
  ramified `ℤ/p^{a+1}`-valued character, provided `p` is prime to the residue characteristic of `A`
  and `μ_{p^{a+1}}` lies in the fixed field of `D_A`.

The group-theoretic part (a) is proved from the identification `D_A ≃* Gal(κ̄/κ)` with the local
Galois group (`localGaloisEquiv`) and the level structure of the tower below `A`; the main
ingredient is that `[D_A : K_L ⊔ I_A] = f_L` where `K_L` is the preimage of the inertia subgroup of
a finite normal level `L/ℚ`.
-/

open SSGRoute

namespace Work.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open NK.TameStructure.ProCyclic

/-! ## Small `Ẑ`-computations -/

/-- Powers in the dense copy of `ℤ` inside `Ẑ`. -/
theorem ofAdd_pow_eq (k : ℤ) (d : ℕ) :
    (Multiplicative.ofAdd k) ^ d = Multiplicative.ofAdd (d * k) := by
  rw [← ofAdd_toAdd (Multiplicative.ofAdd k)]
  congr 1

/-- The target of the `d`-th component map of `Ẑ` has exponent dividing `d`. -/
theorem quot_pow_exp (d : ℕ) (hd : d ≠ 0)
    (g : (Multiplicative ℤ) ⧸ (mZ d hd).toSubgroup) : g ^ d = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  change ((QuotientGroup.mk' (mZ d hd).toSubgroup) a) ^ d = 1
  rw [← map_pow (QuotientGroup.mk' (mZ d hd).toSubgroup) a d, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  rw [← ofAdd_toAdd a, ofAdd_pow_eq a.toAdd d, mem_mZ]
  exact dvd_mul_right (d : ℤ) a.toAdd

/-- The `d`-th power subgroup of `Ẑ` lies in the kernel of the `d`-th component map. -/
theorem powSubgroup_le_ker_compHom (d : ℕ) (hd : d ≠ 0) :
    NK.TowerRank.powSubgroup d ≤ (NK.TameStructure.ProCyclic.compHom d hd).ker := by
  intro z hz
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hz
  rw [← hy, MonoidHom.mem_ker]
  change (NK.TameStructure.ProCyclic.compHom d hd y) ^ d = 1
  exact quot_pow_exp d hd _

/-- The canonical generator of `Ẑ` maps to the class of `1` under the `d`-th component map. -/
theorem compHom_zhatGen_eq (d : ℕ) (hd : d ≠ 0) :
    NK.TameStructure.ProCyclic.compHom d hd NK.TowerRank.zhatGen =
      QuotientGroup.mk (Multiplicative.ofAdd 1) := by
  rw [show NK.TowerRank.zhatGen = NK.TameStructure.ProCyclic.intCastZhat 1 from by
    unfold NK.TowerRank.zhatGen NK.TowerRank.zEta NK.TameStructure.ProCyclic.intCastZhat
    rfl]
  exact NK.TameStructure.ProCyclic.compHom_intCastZhat d hd 1

/-- `quotHom x` sends the class of `1` to `x`. -/
theorem quotHom_one (X : Type*) [Group X] [Finite X] (x : X) :
    (quotHom x) (QuotientGroup.mk (Multiplicative.ofAdd (1 : ℤ))) = x := by
  rw [quotHom, QuotientGroup.lift_mk', zpowersHom_apply, toAdd_ofAdd, zpow_one]

/-! ## Subgroups containing an open subgroup are open -/

/-- A subgroup of a topological group containing an open subset which contains `1` is open. -/
theorem isOpen_subgroup_of_le_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] (H : Subgroup G) {U : Set G} (hU : IsOpen U) (h1 : 1 ∈ U)
    (h : U ⊆ H) : IsOpen (H : Set G) :=
  H.isOpen_of_mem_nhds (Filter.mem_of_superset (hU.mem_nhds h1) h)


/-! ## The level subgroup is open -/

/-- The fixing subgroup of a finite level, as a subgroup of the decomposition group. -/
noncomputable def levelFixSub (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) : Subgroup ↥(SSGRoute.decomp ℚ A'.1) :=
  L.fixingSubgroup.comap (Subgroup.subtype (SSGRoute.decomp ℚ A'.1))

/-- The fixing subgroup of a finite level, as a subgroup of the decomposition group, is open. -/
theorem levelFixSub_isOpen (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] :
    IsOpen (levelFixSub A' L : Set ↥(SSGRoute.decomp ℚ A'.1)) :=
  (IntermediateField.fixingSubgroup_isOpen L).preimage continuous_subtype_val

/-- The kernel of the restriction to a normal level `L` is the fixing subgroup of `L`.

Stated with the ambient algebra structure pinned explicitly, because the instance search for the
`Normal ℚ ↥L` argument of `IntermediateField.restrictNormalHom_ker` is not deterministic in this
file. -/
theorem restrictNormalHom_ker_level (L : IntermediateField ℚ SSGRoute.QBar) [hN : Normal ℚ L] :
    (AlgEquiv.restrictNormalHom L).ker = L.fixingSubgroup :=
  @IntermediateField.restrictNormalHom_ker ℚ SSGRoute.QBar Rat.instField
    (AlgebraicClosure.instField ℚ) (inferInstanceAs (Algebra ℚ SSGRoute.QBar)) L hN

/-- **The level subgroup is open.**  It contains the (open) fixing subgroup of the level. -/
theorem levelSub_isOpen (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [hN : Normal ℚ L]
    [NumberField ↥L] : IsOpen (levelSubQBar A' L : Set ↥(SSGRoute.decomp ℚ A'.1)) := by
  refine isOpen_subgroup_of_le_isOpen (levelSubQBar A' L) (levelFixSub_isOpen A' L)
    (Subgroup.one_mem _) ?_
  intro g hg
  haveI hNi : Normal ℚ ↥L := hN
  have hg' : (g : SSGRoute.GalQ) ∈ L.fixingSubgroup := by
    rw [levelFixSub] at hg
    exact Subgroup.mem_subgroupOf.mp hg
  have h1 : AlgEquiv.restrictNormalHom L (g : SSGRoute.GalQ) = 1 :=
    MonoidHom.mem_ker.mp (restrictNormalHom_ker_level L ▸ hg')
  rw [levelSub_eq_comap_inertia (hN := hN)]
  refine Subgroup.mem_comap.mpr ?_
  show AlgEquiv.restrictNormalHom L (g : SSGRoute.GalQ) ∈
    Ideal.inertia (↥L ≃ₐ[ℚ] ↥L) (levelPrimeQBar A' L).asIdeal
  rw [h1]
  exact Subgroup.one_mem _

/-! ## The engine: preimages of the `d`-th power subgroup are open -/

/-- **The preimage under `localZhatHom` of the `d`-th power subgroup of `Ẑ` is open.**

This is the content of the level structure: the level subgroup `K_L` of a level `L` whose residue
degree `f_L` is divisible by `d` has index `f_L`, so it is mapped into `Ẑ^d ⊆ Ẑ`. -/
theorem localZhatHom_preimage_powSubgroup_isOpen
    (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) (d : ℕ) (hd : 0 < d) :
    IsOpen ((localZhatHom A') ⁻¹' (NK.TowerRank.powSubgroup d) : Set ↥(SSGRoute.decomp ℚ A'.1)) := by
  obtain ⟨L, hL, hLn, hLnf, hdvd⟩ := exists_level_residueDeg A'.1 A'.2 d hd
  haveI : FiniteDimensional ℚ L := hL
  haveI hN : Normal ℚ L := hLn
  haveI : NumberField ↥L := hLnf
  have hle : (localZhatHom A').ker ≤ levelSubQBar A' L ⊔ globalInertiaSub A' := by
    rw [localZhatHom_ker]; exact le_sup_right
  have hmap : ((levelSubQBar A' L ⊔ globalInertiaSub A').map (localZhatHom A')).index =
      (NK.Reconstruct.primeOfLevel A'.1 L (NK.Reconstruct.comap_level_ne_top A'.2 L)).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers ℚ) := by
    rw [Subgroup.index_map_eq (levelSubQBar A' L ⊔ globalInertiaSub A')
      (localZhatHom_surjective A') hle, levelIndex A' L]
  have hpos : 0 < (NK.Reconstruct.primeOfLevel A'.1 L
      (NK.Reconstruct.comap_level_ne_top A'.2 L)).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers ℚ) :=
    Ideal.inertiaDeg_pos _ _
  have hsub : levelSubQBar A' L ⊔ globalInertiaSub A' ≤
      (localZhatHom A') ⁻¹' (NK.TowerRank.powSubgroup d) := by
    intro g hg
    exact zhat_le_of_index hpos hmap hdvd (Subgroup.mem_map_of_mem (localZhatHom A') hg)
  refine isOpen_subgroup_of_le_isOpen
    (Subgroup.comap (localZhatHom A') (NK.TowerRank.powSubgroup d)) (levelSub_isOpen A' L)
    (Subgroup.one_mem _) ?_
  intro g hg
  exact hsub (Subgroup.mem_sup_left hg)

/-! ## Part (a): the universal property of the Frobenius element -/

/-- **Part (a), existence half.**  Every element of a finite group is attained by a continuous
homomorphism `D_A →* X` with open kernel killing the inertia subgroup, evaluated at the Frobenius
element. -/
theorem exists_hom_at_frob (A : ValuationSubring SSGRoute.QBar)
    (hA : SSGRoute.IsFinPlace ℚ A) (X : Type*) [Group X] [Finite X] (x : X) :
    ∃ f : ↥(SSGRoute.decomp ℚ A) →* X,
      IsOpen (f.ker : Set ↥(SSGRoute.decomp ℚ A)) ∧
      (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.IsInertia ℚ A σ → f σ = 1) ∧
      f (localFrobElem ⟨A, hA⟩) = x := by
  set A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar := ⟨A, hA⟩ with hA'
  set d : ℕ := orderOf x with hddef
  have hd : 0 < d := orderOf_pos x
  have hdne : d ≠ 0 := hd.ne'
  refine ⟨(quotHom x).comp ((NK.TameStructure.ProCyclic.compHom d hdne).comp
    (localZhatHom A')), ?_, ?_, ?_⟩
  · have hone : (1 : ↥(SSGRoute.decomp ℚ A)) ∈
        (localZhatHom A') ⁻¹' (NK.TowerRank.powSubgroup d) := by
      show localZhatHom A' 1 ∈ NK.TowerRank.powSubgroup d
      rw [map_one]
      exact Subgroup.one_mem _
    refine isOpen_subgroup_of_le_isOpen _
      (localZhatHom_preimage_powSubgroup_isOpen A' d hd) hone ?_
    intro g hg
    change ((quotHom x).comp ((NK.TameStructure.ProCyclic.compHom d hdne).comp
      (localZhatHom A'))) g = 1
    simp only [MonoidHom.comp_apply]
    rw [show (NK.TameStructure.ProCyclic.compHom d hdne) (localZhatHom A' g) = 1 from
      powSubgroup_le_ker_compHom d hdne hg, map_one]
  · intro σ hσ
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    have h1 : localZhatHom A' σ = 1 := by
      rw [← MonoidHom.mem_ker, localZhatHom_ker]
      exact Subgroup.subset_closure hσ
    rw [h1, map_one, map_one]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, localZhatHom_localFrobElem,
      compHom_zhatGen_eq d hdne]
    exact quotHom_one X x

/-- **Part (a), uniqueness half.**  Two continuous homomorphisms `D_A →* X` (`X` finite) with open
kernels killing the inertia subgroup which agree on the Frobenius element are equal. -/
theorem eq_of_apply_frob_eq (A : ValuationSubring SSGRoute.QBar)
    (hA : SSGRoute.IsFinPlace ℚ A) (X : Type*) [Group X] [Finite X]
    (f g : ↥(SSGRoute.decomp ℚ A) →* X)
    (hf : IsOpen (f.ker : Set ↥(SSGRoute.decomp ℚ A)))
    (hg : IsOpen (g.ker : Set ↥(SSGRoute.decomp ℚ A)))
    (hfi : ∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.IsInertia ℚ A σ → f σ = 1)
    (hgi : ∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.IsInertia ℚ A σ → g σ = 1)
    (hF : f (localFrobElem ⟨A, hA⟩) = g (localFrobElem ⟨A, hA⟩)) : f = g := by
  classical
  set A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar := ⟨A, hA⟩ with hA'
  have hfker : (localZhatHom A').ker ≤ f.ker := by
    rw [localZhatHom_ker]
    exact (Subgroup.closure_le f.ker).mpr fun σ hσ => by
        exact MonoidHom.mem_ker.mpr (hfi σ hσ)
  have hgker : (localZhatHom A').ker ≤ g.ker := by
    rw [localZhatHom_ker]
    exact (Subgroup.closure_le g.ker).mpr fun σ hσ => by
        exact MonoidHom.mem_ker.mpr (hgi σ hσ)
  let ef : (↥(SSGRoute.decomp ℚ A) ⧸ (localZhatHom A').ker) ≃*
      NK.LocalAnabelian.Zhat :=
    QuotientGroup.quotientKerEquivOfSurjective (localZhatHom A') (localZhatHom_surjective A')
  let ψf : NK.LocalAnabelian.Zhat →* X :=
    (QuotientGroup.lift _ f hfker).comp ef.symm.toMonoidHom
  let ψg : NK.LocalAnabelian.Zhat →* X :=
    (QuotientGroup.lift _ g hgker).comp ef.symm.toMonoidHom
  have hef : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      ef (QuotientGroup.mk' (localZhatHom A').ker σ) = localZhatHom A' σ := by
    intro σ
    change QuotientGroup.kerLift (localZhatHom A')
      (QuotientGroup.mk' (localZhatHom A').ker σ) = localZhatHom A' σ
    rw [QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk]
  have hψf : ∀ σ : ↥(SSGRoute.decomp ℚ A), ψf (localZhatHom A' σ) = f σ := by
    intro σ
    show QuotientGroup.lift _ f hfker (ef.symm (localZhatHom A' σ)) = f σ
    rw [← hef σ, MulEquiv.symm_apply_apply]
    exact QuotientGroup.lift_mk' _ _ σ
  have hψg : ∀ σ : ↥(SSGRoute.decomp ℚ A), ψg (localZhatHom A' σ) = g σ := by
    intro σ
    show QuotientGroup.lift _ g hgker (ef.symm (localZhatHom A' σ)) = g σ
    rw [← hef σ, MulEquiv.symm_apply_apply]
    exact QuotientGroup.lift_mk' _ _ σ
  have hpow : ∀ ψ : NK.LocalAnabelian.Zhat →* X,
      NK.TowerRank.powSubgroup (Nat.card X) ≤ ψ.ker := by
    intro ψ z hz
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hz
    have hy' : y ^ Nat.card X = z := by simpa [NK.TowerRank.powHom] using hy
    haveI : Fintype X := Fintype.ofFinite X
    refine MonoidHom.mem_ker.mpr ?_
    rw [← hy', map_pow, Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  have hgen : ψf NK.TowerRank.zhatGen = ψg NK.TowerRank.zhatGen := by
    have h1 : ψf (localZhatHom A' (localFrobElem A')) = f (localFrobElem A') := hψf _
    have h2 : ψg (localZhatHom A' (localFrobElem A')) = g (localFrobElem A') := hψg _
    have h3 : NK.TowerRank.zhatGen = localZhatHom A' (localFrobElem A') :=
      (localZhatHom_localFrobElem A').symm
    rw [h3, h1, h2]
    exact hF
  have hψfg : ψf = ψg := by
    have hcard : 0 < Nat.card X := Nat.card_pos
    have htop := zpowers_zhatGen_sup_powSubgroup (Nat.card X) hcard
    refine MonoidHom.ext fun z => ?_
    have hz : z ∈ (⊤ : Subgroup NK.LocalAnabelian.Zhat) := Subgroup.mem_top z
    rw [← htop] at hz
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hz
    rw [← hab, map_mul, map_mul]
    congr 1
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [map_zpow, map_zpow, hgen]
    · rw [show ψf b = 1 from MonoidHom.mem_ker.mp (hpow ψf hb),
        show ψg b = 1 from MonoidHom.mem_ker.mp (hpow ψg hb)]
  refine MonoidHom.ext fun σ => ?_
  rw [← hψf σ, ← hψg σ, hψfg]

/-! ## Part (b): lifting a totally ramified `p`-power character

The lifting argument is a Kummer-theoretic one and is not yet formalised here; the statement is
recorded so that the assembly below has the exact shape of the target. -/

/-- **Part (b).** -/
theorem exists_lift_totally_ramified (p a : ℕ) (hp : p.Prime)
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsFinPlace ℚ A)
    (hval : ¬ A.valuation (p : SSGRoute.QBar) < 1)
    (hμ : ∃ ζ : SSGRoute.QBar, IsPrimitiveRoot ζ (p ^ (a + 1)) ∧
      ∀ σ ∈ SSGRoute.decomp ℚ A, σ ζ = ζ)
    (χ : ↥(SSGRoute.decomp ℚ A) →* Multiplicative (ZMod (p ^ a)))
    (hopen : IsOpen (χ.ker : Set ↥(SSGRoute.decomp ℚ A)))
    (hiner : ∀ σ : ↥(SSGRoute.decomp ℚ A), ∃ τ : ↥(SSGRoute.decomp ℚ A),
      SSGRoute.IsInertia ℚ A τ ∧ χ τ = χ σ) :
    ∃ χ' : ↥(SSGRoute.decomp ℚ A) →* Multiplicative (ZMod (p ^ (a + 1))),
      IsOpen (χ'.ker : Set ↥(SSGRoute.decomp ℚ A)) ∧
      (∀ σ : ↥(SSGRoute.decomp ℚ A), ∃ τ : ↥(SSGRoute.decomp ℚ A),
        SSGRoute.IsInertia ℚ A τ ∧ χ' τ = χ' σ) ∧
      ∀ σ : ↥(SSGRoute.decomp ℚ A),
        Multiplicative.toAdd (χ σ) =
          ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))
            (Multiplicative.toAdd (χ' σ)) :=
  ramified_char_lift p a hp A hA hval hμ χ hopen hiner

open SSGRoute
theorem local_tame_lifting :
    (∀ (A : ValuationSubring SSGRoute.QBar), SSGRoute.IsFinPlace ℚ A →
      ∃ F : ↥(SSGRoute.decomp ℚ A),
        (∀ (X : Type) [Group X] [Finite X] (x : X),
          ∃ f : ↥(SSGRoute.decomp ℚ A) →* X, IsOpen (f.ker : Set ↥(SSGRoute.decomp ℚ A)) ∧
            (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.IsInertia ℚ A σ → f σ = 1) ∧ f F = x) ∧
        (∀ (X : Type) [Group X] [Finite X] (f g : ↥(SSGRoute.decomp ℚ A) →* X),
          IsOpen (f.ker : Set ↥(SSGRoute.decomp ℚ A)) → IsOpen (g.ker : Set ↥(SSGRoute.decomp ℚ A)) →
          (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.IsInertia ℚ A σ → f σ = 1) →
          (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.IsInertia ℚ A σ → g σ = 1) →
          f F = g F → f = g)) ∧
    (∀ (p a : ℕ), p.Prime → ∀ (A : ValuationSubring SSGRoute.QBar), SSGRoute.IsFinPlace ℚ A →
      ¬ A.valuation (p : SSGRoute.QBar) < 1 →
      (∃ ζ : SSGRoute.QBar, IsPrimitiveRoot ζ (p ^ (a + 1)) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, σ ζ = ζ) →
      ∀ χ : ↥(SSGRoute.decomp ℚ A) →* Multiplicative (ZMod (p ^ a)),
        IsOpen (χ.ker : Set ↥(SSGRoute.decomp ℚ A)) →
        (∀ σ : ↥(SSGRoute.decomp ℚ A), ∃ τ : ↥(SSGRoute.decomp ℚ A),
          SSGRoute.IsInertia ℚ A τ ∧ χ τ = χ σ) →
        ∃ χ' : ↥(SSGRoute.decomp ℚ A) →* Multiplicative (ZMod (p ^ (a + 1))),
          IsOpen (χ'.ker : Set ↥(SSGRoute.decomp ℚ A)) ∧
          (∀ σ : ↥(SSGRoute.decomp ℚ A), ∃ τ : ↥(SSGRoute.decomp ℚ A),
            SSGRoute.IsInertia ℚ A τ ∧ χ' τ = χ' σ) ∧
          ∀ σ : ↥(SSGRoute.decomp ℚ A),
            Multiplicative.toAdd (χ σ) =
              ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))
                (Multiplicative.toAdd (χ' σ))) := by
  refine ⟨?_, ?_⟩
  · intro A hA
    exact ⟨localFrobElem ⟨A, hA⟩,
      fun X _ _ x => exists_hom_at_frob A hA X x,
      fun X _ _ f g hf hg hfi hgi hF => eq_of_apply_frob_eq A hA X f g hf hg hfi hgi hF⟩
  · intro p a hp A hA hval hμ χ hopen hiner
    exact exists_lift_totally_ramified p a hp A hA hval hμ χ hopen hiner

end Work.SSGRoute

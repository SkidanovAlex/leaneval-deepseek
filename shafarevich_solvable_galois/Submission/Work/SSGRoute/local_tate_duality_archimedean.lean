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
import Submission.Work.SSGRoute.LTDArch.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

namespace ArchAux

theorem exists_isOpen_subgroup_not_mem {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) (hc1 : c ≠ 1) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ u ∈ U, u ∈ Subgroup.zpowers c → u = 1 := by
  obtain ⟨x, hx⟩ := DFunLike.exists_ne hc1
  haveI : Algebra.IsIntegral k Ω := Algebra.IsAlgebraic.isIntegral
  let F : IntermediateField k Ω := IntermediateField.adjoin k {x}
  haveI hF : FiniteDimensional k F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hcF : c ∉ F.fixingSubgroup := by
    intro hmem
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem
    refine hx (hmem x ?_)
    exact IntermediateField.subset_adjoin k ({x} : Set Ω) (Set.mem_singleton x)
  refine ⟨F.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen F, ?_⟩
  intro u hu huzp
  rcases Ach.mem_zpowers_eq_one_or c hc huzp with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hu) hcF

section Conc

variable {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
  [DistribMulAction G M]

noncomputable def conc (c : Γ) (m : M) : Γ → M := by
  classical
  exact fun x => if x = c then m else 0

@[simp] lemma conc_self (c : Γ) (m : M) : conc c m c = m := by
  classical
  simp [conc]

lemma conc_of_ne {x : Γ} (c : Γ) (m : M) (hx : x ≠ c) : conc c m x = 0 := by
  classical
  simp [conc, hx]

lemma isCocycleOn_conc (act : Γ →* G) (c : Γ) (hc : c ^ 2 = 1) (hc1 : c ≠ 1) (m : M)
    (hm : m + act c • m = 0) :
    SSGRoute.IsCocycleOn act (Subgroup.zpowers c) (conc c m) := by
  rw [Ach.isCocycleOn_zpowers_iff act c hc]
  exact ⟨conc_of_ne c m (Ne.symm hc1), by rw [conc_self]; exact hm⟩

lemma isLocConstOn_conc (c : Γ) (m : M) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    (hUdisj : ∀ u ∈ U, u ∈ Subgroup.zpowers c → u = 1) :
    SSGRoute.IsLocConstOn (Subgroup.zpowers c) (conc c m) := by
  refine ⟨U, hU, ?_⟩
  intro g hg u hu huH
  rw [hUdisj u hu huH, mul_one]

theorem exists_cocycle_locConst_conc (act : Γ →* G) (c : Γ) (hc : c ^ 2 = 1) (hc1 : c ≠ 1)
    (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    (hUdisj : ∀ u ∈ U, u ∈ Subgroup.zpowers c → u = 1) (m : M)
    (hm : m + act c • m = 0) :
    ∃ f : Γ → M, SSGRoute.IsCocycleOn act (Subgroup.zpowers c) f ∧
      SSGRoute.IsLocConstOn (Subgroup.zpowers c) f ∧ f c = m :=
  ⟨conc c m, isCocycleOn_conc act c hc hc1 m hm, isLocConstOn_conc c m U hU hUdisj, conc_self c m⟩

end Conc

section Op

variable {p : ℕ} [Fact p.Prime] {G M : Type} [Group G] [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction G M] [SMulCommClass G (ZMod p) M]

noncomputable def onePlus (σ : G) : M →ₗ[ZMod p] M :=
  1 + DistribSMul.toLinearMap (ZMod p) M σ

lemma onePlus_apply (σ : G) (y : M) : onePlus (p := p) σ y = y + σ • y := by
  simp [onePlus, DistribSMul.toLinearMap]

lemma dualSMul_apply_of_inv_eq_self (σ : G) (hσ : σ⁻¹ = σ) (ψ : DualMod p M) (y : M) :
    (σ • ψ) y = ψ (σ • y) := by
  rw [DualMod.dualSMul_apply, hσ]

lemma onePlus_dualMap_apply (σ : G) (ψ : DualMod p M) (y : M) :
    (onePlus (p := p) σ).dualMap ψ y = ψ y + ψ (σ • y) := by
  rw [LinearMap.dualMap_apply, onePlus_apply, map_add]

lemma dualMap_onePlus (σ : G) (hσ : σ⁻¹ = σ) (ψ : DualMod p M) :
    (onePlus (p := p) σ).dualMap ψ = σ • ψ + ψ := by
  ext y
  rw [onePlus_dualMap_apply, ← dualSMul_apply_of_inv_eq_self σ hσ, LinearMap.add_apply, add_comm]

end Op

theorem isCoboundaryOn_of_isCocycleOn_of_ne_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (c : Γ) (hc : c ^ 2 = 1) (f : Γ → M)
    (hf : SSGRoute.IsCocycleOn act (Subgroup.zpowers c) f) :
    SSGRoute.IsCoboundaryOn act (Subgroup.zpowers c) f := by
  obtain ⟨hf1, hfc⟩ := (Ach.isCocycleOn_zpowers_iff act c hc f).mp hf
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    exact hp (le_antisymm hle hge)
  have hσv : act c • f c = -f c := eq_neg_of_add_eq_zero_right hfc
  have hsum : (2⁻¹ : ZMod p) + 2⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ h2]
  refine (Ach.isCoboundaryOn_zpowers_iff act c hc f).mpr
    ⟨hf1, -(2⁻¹ : ZMod p) • f c, ?_⟩
  have h1 : act c • (-(2⁻¹ : ZMod p) • f c) = (2⁻¹ : ZMod p) • f c := by
    rw [smul_comm (act c) (-(2⁻¹ : ZMod p)) (f c), hσv, neg_smul_neg]
  have h2' : - (-(2⁻¹ : ZMod p) • f c) = (2⁻¹ : ZMod p) • f c := by
    rw [neg_smul, neg_neg]
  rw [h1, sub_eq_add_neg, h2', ← add_smul, hsum, one_smul]

end ArchAux

theorem local_tate_duality_archimedean (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    ∃ pair : ((Ω ≃ₐ[k] Ω) → E) →
        ((Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) → ZMod p,
      (∀ (f f' g : (Ω ≃ₐ[k] Ω) → E)
          (g' g'' : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f' ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f') →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g' ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g') →
        pair (f + f') g' = pair f g' + pair f' g') ∧
      (∀ (g g' : (Ω ≃ₐ[k] Ω) → E)
          (f f' : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f' ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f') →
        pair g (f + f') = pair g f + pair g f') ∧
      (∀ (f : (Ω ≃ₐ[k] Ω) → E)
          (g : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) f →
        pair f g = 0) ∧
      (∀ (f : (Ω ≃ₐ[k] Ω) → E)
          (g : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) g →
        pair f g = 0) ∧
      (∀ (f : (Ω ≃ₐ[k] Ω) → E),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        (∀ g : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T),
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) → pair f g = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) f) ∧
      (∀ (g : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) →
        (∀ f : (Ω ≃ₐ[k] Ω) → E,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) → pair f g = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) g) := by
  classical
  have hfin : Module.finrank (ZMod p) T = 1 := hT.1
  have hσinv : (SSGRoute.res k K c)⁻¹ = SSGRoute.res k K c :=
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, ← pow_two, hc, map_one])
  have hTtriv : p = 2 → ∀ (σ : Ω ≃ₐ[k] Ω) (t : T), SSGRoute.res k K σ • t = t := by
    intro hp2 σ t
    subst hp2
    have hz : ζ = -1 := IsPrimitiveRoot.eq_neg_one_of_two_right hζ
    have hσζ : σ • ζ = ζ ^ 1 := by rw [hz, pow_one]; simp
    have := hT.2 σ 1 hσζ t
    simpa using this
  have htoE : p = 2 → ∀ (σ : Ω ≃ₐ[k] Ω) (y : E ⊗[ZMod p] T),
      Ach.toE p E T (Ach.coord p T hfin) (SSGRoute.res k K σ • y) =
        SSGRoute.res k K σ • Ach.toE p E T (Ach.coord p T hfin) y := by
    intro hp2 σ y
    subst hp2
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e t =>
        show Ach.coord 2 T hfin (SSGRoute.res k K σ • t) • (SSGRoute.res k K σ • e) =
          SSGRoute.res k K σ • (Ach.coord 2 T hfin t • e)
        rw [hTtriv rfl σ t, smul_comm (SSGRoute.res k K σ) (Ach.coord 2 T hfin t) e]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hAB : ∀ y : E ⊗[ZMod p] T,
      Ach.toE p E T (Ach.coord p T hfin) y ⊗ₜ[ZMod p] Ach.t0 p T hfin = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e t => rw [Ach.toE_tmul, TensorProduct.smul_tmul, Ach.smul_coord_t0]
    | add x y hx hy => rw [map_add, TensorProduct.add_tmul, hx, hy]
  refine ⟨Ach.archPair p (Ω ≃ₐ[k] Ω) E T hfin c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f f' g g' g'' hf hf' hg'
    by_cases hp2 : p = 2
    · rw [Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c (f + f') g',
        Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f g',
        Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f' g']
      simp only [Pi.add_apply, TensorProduct.add_tmul, map_add]
    · rw [Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c (f + f') g',
        Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f g',
        Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f' g', add_zero]
  · intro g g' f f' h5 h6 h7
    by_cases hp2 : p = 2
    · rw [Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g (f + f'),
        Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g f,
        Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g f']
      simp only [Pi.add_apply, LinearMap.add_apply]
    · rw [Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g (f + f'),
        Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g f,
        Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g f', add_zero]
  · intro f g hf hg hfb
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨-, m, hm⟩ := (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc f).mp hfb
      obtain ⟨-, hgc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc g).mp hg.1
      have hψzero : (ArchAux.onePlus (p := 2) (SSGRoute.res k K c)).dualMap (g c) = 0 := by
        rw [ArchAux.dualMap_onePlus (SSGRoute.res k K c) hσinv, add_comm]
        exact hgc
      rw [Ach.archPair_apply_of_eq_two (h := hfin) 2 (Ω ≃ₐ[k] Ω) E T rfl c f g]
      have hkey : f c = SSGRoute.res k K c • m + m := by
        rw [hm, Ach.sub_eq_add_of_eq_two 2 rfl]
      have hsmul : (SSGRoute.res k K c • m) ⊗ₜ[ZMod 2] Ach.t0 2 T hfin =
          SSGRoute.res k K c • (m ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) := by
        rw [show SSGRoute.res k K c • (m ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) =
            (SSGRoute.res k K c • m) ⊗ₜ[ZMod 2] (SSGRoute.res k K c • Ach.t0 2 T hfin) from rfl,
          hTtriv rfl c (Ach.t0 2 T hfin)]
      have h2 : f c ⊗ₜ[ZMod 2] Ach.t0 2 T hfin =
          ArchAux.onePlus (p := 2) (SSGRoute.res k K c) (m ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) := by
        rw [hkey, ArchAux.onePlus_apply, TensorProduct.add_tmul, ← hsmul, add_comm]
      rw [h2, ← LinearMap.dualMap_apply, hψzero, LinearMap.zero_apply]
    · rw [Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f g]
  · intro f g hf hg hgb
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨-, ψ₀, hψ₀⟩ := (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc g).mp hgb
      obtain ⟨-, hfc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc f).mp hf.1
      rw [Ach.archPair_apply_of_eq_two (h := hfin) 2 (Ω ≃ₐ[k] Ω) E T rfl c f g]
      have hgc : g c = SSGRoute.res k K c • ψ₀ + ψ₀ := by
        rw [hψ₀, Ach.sub_eq_add_of_eq_two 2 rfl]
      have hsmul : (SSGRoute.res k K c • f c) ⊗ₜ[ZMod 2] Ach.t0 2 T hfin =
          SSGRoute.res k K c • (f c ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) := by
        rw [show SSGRoute.res k K c • (f c ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) =
            (SSGRoute.res k K c • f c) ⊗ₜ[ZMod 2] (SSGRoute.res k K c • Ach.t0 2 T hfin) from rfl,
          hTtriv rfl c (Ach.t0 2 T hfin)]
      have hx : SSGRoute.res k K c • (f c ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) +
          (f c ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) = 0 := by
        rw [← hsmul, ← TensorProduct.add_tmul, add_comm, hfc, TensorProduct.zero_tmul]
      rw [hgc, LinearMap.add_apply, ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv, ← map_add, hx,
        map_zero]
    · rw [Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f g]
  · intro f hf hzero
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨hf1, hfc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc f).mp hf.1
      by_cases hc1 : c = 1
      · refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc f).mpr ⟨hf1, 0, ?_⟩
        rw [hc1, hf1, map_one, one_smul, sub_self]
      · obtain ⟨U, hUopen, hUdisj⟩ := ArchAux.exists_isOpen_subgroup_not_mem c hc hc1
        have hsmul : ∀ e : E, (SSGRoute.res k K c • e) ⊗ₜ[ZMod 2] Ach.t0 2 T hfin =
            SSGRoute.res k K c • (e ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) := by
          intro e
          rw [show SSGRoute.res k K c • (e ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) =
              (SSGRoute.res k K c • e) ⊗ₜ[ZMod 2] (SSGRoute.res k K c • Ach.t0 2 T hfin) from rfl,
            hTtriv rfl c (Ach.t0 2 T hfin)]
        have hmem : f c ∈ (ArchAux.onePlus (p := 2) (SSGRoute.res k K c) : E →ₗ[ZMod 2] E).range := by
          rw [Ach.mem_range_iff_forall_dual]
          intro φ hφ
          have hφ' : φ + SSGRoute.res k K c • φ = 0 := by
            ext v
            rw [LinearMap.add_apply, LinearMap.zero_apply,
              ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv, ← map_add,
              ← ArchAux.onePlus_apply (p := 2) (SSGRoute.res k K c) v]
            exact hφ v
          set ψ : SSGRoute.DualMod 2 (E ⊗[ZMod 2] T) :=
            φ.comp (Ach.toE 2 E T (Ach.coord 2 T hfin)) with hψdef
          have hψinv : ∀ y : E ⊗[ZMod 2] T, ψ (SSGRoute.res k K c • y) = ψ y := by
            intro y
            show φ (Ach.toE 2 E T (Ach.coord 2 T hfin) (SSGRoute.res k K c • y)) =
              φ (Ach.toE 2 E T (Ach.coord 2 T hfin) y)
            rw [htoE rfl c y, ← ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv]
            have h2 := DFunLike.congr_fun hφ' (Ach.toE 2 E T (Ach.coord 2 T hfin) y)
            rw [LinearMap.add_apply, LinearMap.zero_apply] at h2
            exact ((Ach.add_eq_zero_iff_eq_of_eq_two 2 rfl _ _).mp h2).symm
          have hψfix : ψ + SSGRoute.res k K c • ψ = 0 := by
            have hs : SSGRoute.res k K c • ψ = ψ := LinearMap.ext fun y => by
              rw [ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv, hψinv y]
            rw [hs]
            exact Ach.add_self_eq_zero_of_eq_two 2 rfl ψ
          obtain ⟨g, hg1, hg2, hgc⟩ := ArchAux.exists_cocycle_locConst_conc (SSGRoute.res k K) c hc hc1
            U hUopen hUdisj ψ hψfix
          have h0 := hzero g ⟨hg1, hg2⟩
          rw [Ach.archPair_apply_of_eq_two (h := hfin) 2 (Ω ≃ₐ[k] Ω) E T rfl c f g, hgc,
            hψdef, LinearMap.comp_apply, Ach.toE_tmul, Ach.coord_t0, one_smul] at h0
          exact h0
        obtain ⟨m, hm⟩ := hmem
        refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc f).mpr ⟨hf1, m, ?_⟩
        rw [Ach.sub_eq_add_of_eq_two 2 rfl, ← hm, ArchAux.onePlus_apply, add_comm]
    · exact ArchAux.isCoboundaryOn_of_isCocycleOn_of_ne_two p hp2 (SSGRoute.res k K) c hc f hf.1
  · intro g hg hzero
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨hg1, hgc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc g).mp hg.1
      by_cases hc1 : c = 1
      · refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc g).mpr ⟨hg1, 0, ?_⟩
        rw [hc1, hg1, map_one, one_smul, sub_self]
      · obtain ⟨U, hUopen, hUdisj⟩ := ArchAux.exists_isOpen_subgroup_not_mem c hc hc1
        have hψinv : ∀ y : E ⊗[ZMod 2] T, (g c) (SSGRoute.res k K c • y) = (g c) y := by
          intro y
          have h2 := DFunLike.congr_fun hgc y
          rw [LinearMap.add_apply, LinearMap.zero_apply,
            ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv] at h2
          exact ((Ach.add_eq_zero_iff_eq_of_eq_two 2 rfl _ _).mp h2).symm
        have hBop : ∀ y : E ⊗[ZMod 2] T,
            ArchAux.onePlus (p := 2) (SSGRoute.res k K c) (Ach.toE 2 E T (Ach.coord 2 T hfin) y) =
              Ach.toE 2 E T (Ach.coord 2 T hfin) (ArchAux.onePlus (p := 2) (SSGRoute.res k K c) y) := by
          intro y
          rw [ArchAux.onePlus_apply, ArchAux.onePlus_apply, map_add, htoE rfl c y]
        have hker : ∀ y : E ⊗[ZMod 2] T,
            ArchAux.onePlus (p := 2) (SSGRoute.res k K c) y = 0 → (g c) y = 0 := by
          intro y hy
          obtain ⟨f, hf1, hf2, hfc⟩ := ArchAux.exists_cocycle_locConst_conc (SSGRoute.res k K) c hc hc1
            U hUopen hUdisj (Ach.toE 2 E T (Ach.coord 2 T hfin) y) (by rw [← ArchAux.onePlus_apply (p := 2) (SSGRoute.res k K c) (Ach.toE 2 E T (Ach.coord 2 T hfin) y), hBop, hy, map_zero])
          have h0 := hzero f ⟨hf1, hf2⟩
          rw [Ach.archPair_apply_of_eq_two (h := hfin) 2 (Ω ≃ₐ[k] Ω) E T rfl c f g, hfc] at h0
          rwa [hAB y] at h0
        have hmem : (g c) ∈ (ArchAux.onePlus (p := 2) (SSGRoute.res k K c) :
            (E ⊗[ZMod 2] T) →ₗ[ZMod 2] (E ⊗[ZMod 2] T)).dualMap.range := by
          rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
          intro y hy
          exact hker y (by simpa using hy)
        obtain ⟨ψ₀, hψ₀⟩ := hmem
        refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc g).mpr ⟨hg1, ψ₀, ?_⟩
        rw [Ach.sub_eq_add_of_eq_two 2 rfl]
        refine LinearMap.ext fun y => ?_
        rw [← hψ₀, ArchAux.onePlus_dualMap_apply, ← ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv,
          LinearMap.add_apply, add_comm]
    · exact ArchAux.isCoboundaryOn_of_isCocycleOn_of_ne_two p hp2 (SSGRoute.res k K) c hc g hg.1

end Work.SSGRoute

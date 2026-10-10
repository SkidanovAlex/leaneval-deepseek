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
import Submission.Work.SSGRoute.prop5.magnusGroupPart
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus leading term of an element of `γ_j` lies in the nested span

For the free group `F = FreeGroup X` and its lower central series (Mathlib indexing
`(⊤ : Subgroup F).lowerCentralSeries k` for the paper's `γ_{k+1}`), the leading term
`magLead (j+1) z` of an element `z ∈ γ_j` is the image modulo `fil X (j+1)` of an element of the
"nested span" `nestedSpan X j` (the `ℤ`-span of the left-nested bracket monomials `lnMon w`,
`|w| = j`).

The proof is an induction on `j`:
* `γ_j = ⁅γ_{j-1}, ⊤⁆` is the closure of the commutators `⁅u,v⁆`, `u ∈ γ_{j-1}`, `v ∈ F`;
* the degree-`j` component of `magLead` is additive on `γ_j` and converts a group commutator
  `⁅u,v⁆` into the ring commutator of the degree components of `u` and `v` (``magLead_commutator``);
* the nested span is closed under the ring commutator (`nestedSpan_bracket_le`).

The extraction of the degree components is done with the projection `degPart j` of
`FreeAssoc X = ℤ[FreeMonoid X]` onto the words of length `j`.
-/

noncomputable section

set_option maxHeartbeats 8000000

open scoped commutatorElement
attribute [local instance] Classical.propDecidable

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-! ## The degree projection of the free associative algebra -/

/-- The projection of `FreeAssoc X = ℤ[FreeMonoid X]` onto the words of length `j` (the "degree
`j` part"). -/
noncomputable def degPart (j : ℕ) : FreeAssoc X →ₗ[ℤ] FreeAssoc X where
  toFun a := MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j) a.coeff)
  map_add' a b := by
    apply MonoidAlgebra.ext
    ext w
    show (MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j)
      (a + b).coeff)).coeff w = _
    rw [MonoidAlgebra.coeff_add, Finsupp.filter_add, Finsupp.add_apply]
    rfl
  map_smul' c a := by
    apply MonoidAlgebra.ext
    ext w
    show (MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j)
      (c • a).coeff)).coeff w = _
    rw [MonoidAlgebra.coeff_smul, Finsupp.filter_smul, Finsupp.smul_apply]
    rfl

theorem coeff_degPart (j : ℕ) (a : FreeAssoc X) (w : FreeMonoid X) :
    (degPart (X:=X) j a).coeff w = if w.length = j then a.coeff w else 0 := by
  show (MonoidAlgebra.ofCoeff (Finsupp.filter (fun w : FreeMonoid X => w.length = j)
    a.coeff)).coeff w = _
  rw [Finsupp.filter_apply]

theorem coeff_single_fa (w v : FreeMonoid X) (r : ℤ) :
    (MonoidAlgebra.single w r : FreeAssoc X).coeff v = if v = w then r else 0 := by
  rw [MonoidAlgebra.coeff_single]
  by_cases h : v = w
  · subst h; rw [if_pos rfl, Finsupp.single_eq_same]
  · rw [if_neg h, Finsupp.single_eq_of_ne h]

theorem degPart_single (j : ℕ) (w : FreeMonoid X) (r : ℤ) :
    degPart (X:=X) j (MonoidAlgebra.single w r)
      = if w.length = j then MonoidAlgebra.single w r else 0 := by
  apply MonoidAlgebra.ext; ext v
  rw [coeff_degPart, coeff_single_fa]
  have hR : ((if w.length = j then (MonoidAlgebra.single w r : FreeAssoc X) else 0)).coeff v
      = (if w.length = j then (if v = w then r else 0) else 0) := by
    by_cases h : w.length = j
    · rw [if_pos h, if_pos h, coeff_single_fa]
    · rw [if_neg h, if_neg h, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  rw [hR]
  by_cases hv : v = w
  · subst hv; rfl
  · rw [if_neg hv]
    by_cases hw : w.length = j
    · rw [if_pos hw]; split_ifs <;> rfl
    · rw [if_neg hw]; split_ifs <;> rfl

theorem degPart_wordEl (j : ℕ) (w : List X) :
    degPart (X:=X) j (wordEl w) = if w.length = j then wordEl w else 0 := by
  rw [wordEl, degPart_single]
  rfl

theorem single_mem_wordSpan {j : ℕ} {w : FreeMonoid X} (h : w.length = j) (r : ℤ) :
    MonoidAlgebra.single w r ∈ wordSpan (X:=X) j := by
  rw [show MonoidAlgebra.single w r = r • MonoidAlgebra.single w (1:ℤ) by
    rw [MonoidAlgebra.smul_single']; simp]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨FreeMonoid.toList w, h, by rw [wordEl, FreeMonoid.ofList_toList]⟩

theorem degPart_mem_wordSpan (j : ℕ) (a : FreeAssoc X) :
    degPart (X:=X) j a ∈ wordSpan (X:=X) j := by
  have hsum := Finsupp.sum_of_support_subset (degPart (X:=X) j a).coeff
      (s := (degPart (X:=X) j a).coeff.support) (Finset.Subset.refl _)
      (fun w r => MonoidAlgebra.single w r) (fun i hi => by simp)
  rw [show (degPart (X:=X) j a).coeff.sum (fun w r => MonoidAlgebra.single w r) =
      degPart (X:=X) j a from MonoidAlgebra.sum_coeff_single _] at hsum
  rw [hsum]
  refine Submodule.sum_mem _ (fun w hw => ?_)
  have hwj : w.length = j := by
    by_contra hw'
    exact (Finsupp.mem_support_iff.mp hw) (by rw [coeff_degPart, if_neg hw'])
  exact single_mem_wordSpan hwj ((degPart (X:=X) j a).coeff w)

theorem mem_wordSpan_iff (j : ℕ) (a : FreeAssoc X) :
    a ∈ wordSpan (X:=X) j ↔ ∀ w : FreeMonoid X, w.length ≠ j → a.coeff w = 0 := by
  constructor
  · intro h
    refine Submodule.span_induction (p := fun a _ => ∀ w, w.length ≠ j → a.coeff w = 0)
      ?_ ?_ ?_ ?_ h
    · rintro a ⟨u, hu, rfl⟩ w hw
      rw [wordEl, coeff_single_fa, if_neg]
      intro h'
      exact hw (by rw [h']; exact hu)
    · intro w hw; rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    · intro x y _ _ hx hy w hw
      rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx w hw, hy w hw, add_zero]
    · intro c x _ hx w hw
      rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, hx w hw, smul_zero]
  · intro h
    have hsum := Finsupp.sum_of_support_subset a.coeff (s := a.coeff.support) (Finset.Subset.refl _)
        (fun w r => MonoidAlgebra.single w r) (fun i hi => by simp)
    rw [show a.coeff.sum (fun w r => MonoidAlgebra.single w r) = a
        from MonoidAlgebra.sum_coeff_single _] at hsum
    rw [hsum]
    refine Submodule.sum_mem _ (fun w hw => ?_)
    have hwj : w.length = j := by
      by_contra hw'
      exact (Finsupp.mem_support_iff.mp hw) (h w hw')
    exact single_mem_wordSpan hwj (a.coeff w)

theorem degPart_eq_self_of_mem_wordSpan {j : ℕ} {a : FreeAssoc X} (ha : a ∈ wordSpan (X:=X) j) :
    degPart (X:=X) j a = a := by
  apply MonoidAlgebra.ext; ext w
  rw [coeff_degPart]
  by_cases h : w.length = j
  · rw [if_pos h]
  · rw [if_neg h, (mem_wordSpan_iff j a).mp ha w h]

theorem wordSpan_mul_mem {p q : ℕ} {a b : FreeAssoc X}
    (ha : a ∈ wordSpan (X:=X) p) (hb : b ∈ wordSpan (X:=X) q) :
    a * b ∈ wordSpan (X:=X) (p+q) := by
  refine Submodule.span_induction₂ (p := fun a b _ _ => a * b ∈ wordSpan (X:=X) (p+q))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    rw [wordEl, wordEl, MonoidAlgebra.single_mul_single, mul_one]
    rw [show MonoidAlgebra.single (FreeMonoid.ofList u * FreeMonoid.ofList v) (1:ℤ)
        = wordEl (u ++ v) by rw [wordEl, FreeMonoid.ofList_append]]
    exact Submodule.subset_span ⟨u ++ v, by rw [List.length_append, hu, hv], rfl⟩
  · intro y hy; rw [zero_mul]; exact Submodule.zero_mem _
  · intro x hx; rw [mul_zero]; exact Submodule.zero_mem _
  · intro x y z hx hy hz h1 h2; rw [add_mul]; exact Submodule.add_mem _ h1 h2
  · intro x y z hx hy hz h1 h2; rw [mul_add]; exact Submodule.add_mem _ h1 h2
  · intro r x y hx hy h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  · intro r x y hx hy h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

theorem mem_fil_of_mem_wordSpan {j : ℕ} {a : FreeAssoc X} (h : a ∈ wordSpan (X:=X) j) :
    a ∈ fil X j := by
  rw [wordSpan] at h
  rw [fil_eq_filI]
  change a ∈ Submodule.span ℤ (filgen X j)
  exact (Submodule.span_le.mpr (by
    rintro a ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨FreeMonoid.ofList u,
      by rw [show (FreeMonoid.ofList u).length = u.length from rfl, hu], rfl⟩)) h

theorem degPart_eq_zero_of_mem_fil {N j : ℕ} {a : FreeAssoc X} (h : a ∈ fil X N) (hN : j < N) :
    degPart (X:=X) j a = 0 := by
  rw [fil_eq_filI] at h
  change a ∈ Submodule.span ℤ (filgen X N) at h
  refine Submodule.span_induction (p := fun a _ => degPart (X:=X) j a = 0) ?_ ?_ ?_ ?_ h
  · rintro a ⟨w, hw, rfl⟩
    rw [degPart_single, if_neg (by omega)]
  · exact map_zero _
  · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
  · intro c x _ hx; rw [map_smul, hx, smul_zero]

theorem sub_degPart_mem_fil {p : ℕ} {a : FreeAssoc X} (h : a ∈ fil X p) :
    a - degPart (X:=X) p a ∈ fil X (p+1) := by
  rw [fil_eq_filI] at h ⊢
  change a ∈ Submodule.span ℤ (filgen X p) at h
  change a - degPart (X:=X) p a ∈ Submodule.span ℤ (filgen X (p+1))
  refine Submodule.span_induction (p := fun a _ => a - degPart (X:=X) p a ∈
      Submodule.span ℤ (filgen X (p+1))) ?_ ?_ ?_ ?_ h
  · rintro a ⟨w, hw, rfl⟩
    rw [degPart_single]
    by_cases hwj : w.length = p
    · rw [if_pos hwj, sub_self]; exact Submodule.zero_mem _
    · rw [if_neg hwj, sub_zero]
      exact Submodule.subset_span ⟨w, by omega, rfl⟩
  · rw [map_zero, sub_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    rw [show x + y - (degPart (X:=X) p x + degPart (X:=X) p y)
        = (x - degPart (X:=X) p x) + (y - degPart (X:=X) p y) from by abel]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    rw [show c • x - c • degPart (X:=X) p x = c • (x - degPart (X:=X) p x)
        from by rw [smul_sub]]
    exact Submodule.smul_mem _ c hx

theorem degPart_mul_of_mem_fil {p q : ℕ} {a b : FreeAssoc X}
    (ha : a ∈ fil X p) (hb : b ∈ fil X q) :
    degPart (X:=X) (p+q) (a * b) = degPart (X:=X) p a * degPart (X:=X) q b := by
  have ha' : a - degPart (X:=X) p a ∈ fil X (p+1) := sub_degPart_mem_fil ha
  have hb' : b - degPart (X:=X) q b ∈ fil X (q+1) := sub_degPart_mem_fil hb
  have hdpa : degPart (X:=X) p a ∈ fil X p := mem_fil_of_mem_wordSpan (degPart_mem_wordSpan p a)
  have hdqb : degPart (X:=X) q b ∈ fil X q := mem_fil_of_mem_wordSpan (degPart_mem_wordSpan q b)
  have hrest : a * b - degPart (X:=X) p a * degPart (X:=X) q b ∈ fil X (p+q+1) := by
    have heq : a * b - degPart (X:=X) p a * degPart (X:=X) q b
        = degPart (X:=X) p a * (b - degPart (X:=X) q b) + (a - degPart (X:=X) p a) * b := by
      noncomm_ring
    rw [heq]
    refine Submodule.add_mem _ ?_ ?_
    · exact fil_mul_le X p (q+1) (Ideal.mul_mem_mul hdpa hb')
    · have h := fil_mul_le X (p+1) q (Ideal.mul_mem_mul ha' hb)
      rwa [show (p+1)+q = p+q+1 from by omega] at h
  have h1 : degPart (X:=X) (p+q) (a * b - degPart (X:=X) p a * degPart (X:=X) q b) = 0 :=
    degPart_eq_zero_of_mem_fil hrest (by omega)
  have h2 : degPart (X:=X) (p+q) (a * b)
      = degPart (X:=X) (p+q) (degPart (X:=X) p a * degPart (X:=X) q b) := by
    rw [map_sub] at h1
    exact sub_eq_zero.mp h1
  rw [h2, degPart_eq_self_of_mem_wordSpan
    (wordSpan_mul_mem (degPart_mem_wordSpan p a) (degPart_mem_wordSpan q b))]

/-! ## The nested span is closed under the ring commutator -/

/-- The fold `alFold` appends a letter on the right by bracketing. -/
theorem alFold_append_singleton (a : FreeAssoc X) (u : List X) (y : X) :
    alFold a (u ++ [y]) = alFold a u * wordEl [y] - wordEl [y] * alFold a u := by
  rw [alFold, List.foldl_append, alFold]; simp

/-- `lnMon` on a word with one more letter on the right. -/
theorem lnMon_append_singleton (x : X) (u : List X) (y : X) :
    lnMon (x :: (u ++ [y])) = lnMon (x :: u) * wordEl [y] - wordEl [y] * lnMon (x :: u) := by
  rw [lnMon_eq_alFold, lnMon_eq_alFold, alFold_append_singleton]

/-- Bracketing an element of `nestedSpan p` on the right by a generator stays in
`nestedSpan (p+1)`. -/
theorem nestedSpan_bracket_word (p : ℕ) {a : FreeAssoc X}
    (ha : a ∈ nestedSpan (X:=X) p) (y : X) :
    a * wordEl [y] - wordEl [y] * a ∈ nestedSpan (X:=X) (p+1) := by
  refine Submodule.span_induction
    (p := fun a _ => a * wordEl [y] - wordEl [y] * a ∈ nestedSpan (X:=X) (p+1)) ?_ ?_ ?_ ?_ ha
  · rintro a ⟨w, hw, rfl⟩
    rcases w with _ | ⟨x, rest⟩
    · show (0 : FreeAssoc X) * wordEl [y] - wordEl [y] * 0 ∈ nestedSpan (X:=X) (p+1)
      rw [zero_mul, mul_zero, sub_self]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨x :: (rest ++ [y]), ?_, (lnMon_append_singleton x rest y).symm⟩
      simp only [List.length_cons, List.length_append, List.length_nil] at hw ⊢
      omega
  · rw [zero_mul, mul_zero, sub_self]; exact Submodule.zero_mem _
  · intro x z _ _ hx hz
    rw [show (x + z) * wordEl [y] - wordEl [y] * (x + z)
        = (x * wordEl [y] - wordEl [y] * x) + (z * wordEl [y] - wordEl [y] * z)
        from by noncomm_ring]
    exact Submodule.add_mem _ hx hz
  · intro c x _ hx
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ c hx

/-- The key induction: bracketing an element of `nestedSpan p` by a left-nested bracket `lnMon v`
stays in `nestedSpan (p + |v|)`. -/
theorem nestedSpan_bracket_lnMon : ∀ v : List X, ∀ (p : ℕ) (a : FreeAssoc X),
    a ∈ nestedSpan (X:=X) p →
    a * lnMon v - lnMon v * a ∈ nestedSpan (X:=X) (p + v.length) := by
  intro v
  induction v using List.reverseRecOn with
  | nil =>
      intro p a _
      rw [show lnMon (X:=X) ([] : List X) = 0 from rfl, List.length_nil, Nat.add_zero]
      rw [mul_zero, zero_mul, sub_self]; exact Submodule.zero_mem _
  | append_singleton u y ihv =>
      intro p a ha
      rcases u with _ | ⟨x, rest⟩
      · rw [List.nil_append]
        show a * wordEl [y] - wordEl [y] * a ∈ nestedSpan (X:=X) (p + 1)
        exact nestedSpan_bracket_word p ha y
      · change a * lnMon (x :: (rest ++ [y])) - lnMon (x :: (rest ++ [y])) * a ∈
          nestedSpan (X:=X) (p + (x :: (rest ++ [y])).length)
        have h1 : a * lnMon (x :: rest) - lnMon (x :: rest) * a
            ∈ nestedSpan (X:=X) (p + (x :: rest).length) := ihv p a ha
        have h1' : (a * lnMon (x :: rest) - lnMon (x :: rest) * a) * wordEl [y]
            - wordEl [y] * (a * lnMon (x :: rest) - lnMon (x :: rest) * a)
            ∈ nestedSpan (X:=X) (p + (x :: rest).length + 1) :=
          nestedSpan_bracket_word _ h1 y
        have hW : a * wordEl [y] - wordEl [y] * a ∈ nestedSpan (X:=X) (p+1) :=
          nestedSpan_bracket_word p ha y
        have h2 : (a * wordEl [y] - wordEl [y] * a) * lnMon (x :: rest)
            - lnMon (x :: rest) * (a * wordEl [y] - wordEl [y] * a)
            ∈ nestedSpan (X:=X) ((p+1) + (x :: rest).length) := ihv (p+1) _ hW
        have h3 : lnMon (x :: rest) * (a * wordEl [y] - wordEl [y] * a)
            - (a * wordEl [y] - wordEl [y] * a) * lnMon (x :: rest)
            ∈ nestedSpan (X:=X) (p + (x :: rest).length + 1) := by
          have := neg_mem h2
          rwa [show (p+1) + (x :: rest).length = p + (x :: rest).length + 1 from by omega,
            show - ((a * wordEl [y] - wordEl [y] * a) * lnMon (x :: rest)
                - lnMon (x :: rest) * (a * wordEl [y] - wordEl [y] * a))
              = lnMon (x :: rest) * (a * wordEl [y] - wordEl [y] * a)
                - (a * wordEl [y] - wordEl [y] * a) * lnMon (x :: rest) from by noncomm_ring] at this
        rw [lnMon_append_singleton x rest y]
        rw [show (x :: (rest ++ [y])).length = (x :: rest).length + 1 from by simp]
        rw [show a * (lnMon (x :: rest) * wordEl [y] - wordEl [y] * lnMon (x :: rest))
              - (lnMon (x :: rest) * wordEl [y] - wordEl [y] * lnMon (x :: rest)) * a
            = ((a * lnMon (x :: rest) - lnMon (x :: rest) * a) * wordEl [y]
                - wordEl [y] * (a * lnMon (x :: rest) - lnMon (x :: rest) * a))
              + (lnMon (x :: rest) * (a * wordEl [y] - wordEl [y] * a)
                - (a * wordEl [y] - wordEl [y] * a) * lnMon (x :: rest)) from by noncomm_ring]
        exact Submodule.add_mem _ h1' h3

/-- **The nested span is closed under the ring commutator.** -/
theorem nestedSpan_bracket_le {p q : ℕ} {a b : FreeAssoc X}
    (ha : a ∈ nestedSpan (X:=X) p) (hb : b ∈ nestedSpan (X:=X) q) :
    a * b - b * a ∈ nestedSpan (X:=X) (p+q) := by
  refine Submodule.span_induction₂
    (p := fun a b _ _ => a * b - b * a ∈ nestedSpan (X:=X) (p+q)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    have := nestedSpan_bracket_lnMon v p (lnMon u) (Submodule.subset_span ⟨u, hu, rfl⟩)
    rwa [hv] at this
  · intro y _
    rw [zero_mul, mul_zero, sub_self]; exact Submodule.zero_mem _
  · intro x _
    rw [mul_zero, zero_mul, sub_self]; exact Submodule.zero_mem _
  · intro x y z _ _ _ h1 h2
    rw [show (x + y) * z - z * (x + y)
        = (x * z - z * x) + (y * z - z * y) from by noncomm_ring]
    exact Submodule.add_mem _ h1 h2
  · intro x y z _ _ _ h1 h2
    rw [show x * (y + z) - (y + z) * x
        = (x * y - y * x) + (x * z - z * x) from by noncomm_ring]
    exact Submodule.add_mem _ h1 h2
  · intro r x y _ _ h
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ r h
  · intro r x y _ _ h
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
    exact Submodule.smul_mem _ r h

/-! ## The main induction -/

/-- The degree-`1` part of the free associative algebra is contained in the nested span. -/
theorem wordSpan_one_le_nestedSpan : wordSpan (X:=X) 1 ≤ nestedSpan (X:=X) 1 := by
  rw [wordSpan, nestedSpan]
  refine Submodule.span_le.mpr ?_
  rintro a ⟨u, hu, rfl⟩
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hu
  exact Submodule.subset_span ⟨[x], rfl, rfl⟩

/-- **The main induction.**  For `z ∈ γ_j` (`j = m+1`) and any lift `a ∈ fil X j` of the leading
term `magLead N z` (with `N ≥ j+1`), the degree-`j` component `degPart j a` lies in the nested
span. -/
theorem degPart_mem_nestedSpan_of_magLead : ∀ j : ℕ, 1 ≤ j → ∀ (N : ℕ), j+1 ≤ N →
    ∀ z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j-1),
    ∀ a : FreeAssoc X, a ∈ fil X j →
      Ideal.Quotient.mk (fil X N) a = magLead N z →
        degPart (X:=X) j a ∈ nestedSpan (X:=X) j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ m ih =>
      intro hm1 N hN z hz a ha haeq
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- base case `j = 1`
        subst hm0
        exact wordSpan_one_le_nestedSpan (degPart_mem_wordSpan 1 a)
      · -- step `j = m+1`, `m ≥ 1`
        have hzclos : z ∈ Subgroup.closure {g : FreeGroup X |
            ∃ g1 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (m-1),
            ∃ g2 ∈ (⊤ : Subgroup (FreeGroup X)), ⁅g1, g2⁆ = g} := by
          rw [← Subgroup.commutator_def, ← Subgroup.lowerCentralSeries_succ (n := m - 1),
            show m - 1 + 1 = m from by omega]
          exact hz
        have hmem_of : ∀ z ∈ Subgroup.closure {g : FreeGroup X |
              ∃ g1 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (m-1),
              ∃ g2 ∈ (⊤ : Subgroup (FreeGroup X)), ⁅g1, g2⁆ = g},
            z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := by
          intro z hz'
          have h1 : z ∈ ⁅(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (m - 1), (⊤ : Subgroup (FreeGroup X))⁆ := by
            rwa [Subgroup.commutator_def]
          rw [show m = m - 1 + 1 from by omega, Subgroup.lowerCentralSeries_succ]
          exact h1
        revert a ha haeq
        refine Subgroup.closure_induction (p := fun z _ => ∀ a : FreeAssoc X, a ∈ fil X (m+1) →
            Ideal.Quotient.mk (fil X N) a = magLead N z →
              degPart (X:=X) (m+1) a ∈ nestedSpan (X:=X) (m+1)) ?_ ?_ ?_ ?_ hzclos
        · -- generator: `z = ⁅u,v⁆`
          rintro z ⟨u, hu, v, hv, rfl⟩ a ha haeq
          have hv' : v ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (1 - 1) := by
            rw [Nat.sub_self, Subgroup.lowerCentralSeries_zero]; exact hv
          have hU : magLead N u ∈ filq X N m := magLead_mem_filq N m (by omega) (by omega) hu
          have hV : magLead N v ∈ filq X N 1 := magLead_mem_filq N 1 le_rfl (by omega) hv'
          obtain ⟨a_u, ha_u, ha_ueq⟩ :=
            (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hU
          obtain ⟨a_v, ha_v, ha_veq⟩ :=
            (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hV
          have hmc := magLead_commutator N m 1 (by omega) le_rfl (by omega) hu hv'
          rw [← ha_ueq, ← ha_veq] at hmc
          -- the degree `(m+1)` components of `a` and of `⁅a_u,a_v⁆` agree
          have hdiff_deg : degPart (X:=X) (m+1) (a - (a_u * a_v - a_v * a_u)) = 0 := by
            have hmem : Ideal.Quotient.mk (fil X N) (a - (a_u * a_v - a_v * a_u))
                ∈ filq X N (m + 1 + 1) := by
              rw [map_sub, map_sub, map_mul, map_mul, haeq]
              exact hmc
            obtain ⟨d, hd, hdeq⟩ :=
              (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hmem
            have h2 : (a - (a_u * a_v - a_v * a_u)) - d ∈ fil X N := by
              rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hdeq, sub_self]
            have h3 : degPart (X:=X) (m+1) ((a - (a_u * a_v - a_v * a_u)) - d) = 0 :=
              degPart_eq_zero_of_mem_fil h2 (by omega)
            rw [map_sub, sub_eq_zero] at h3
            rw [h3]
            exact degPart_eq_zero_of_mem_fil hd (by omega)
          have hc_deg : degPart (X:=X) (m+1) (a_u * a_v - a_v * a_u)
              = degPart (X:=X) m a_u * degPart (X:=X) 1 a_v
                - degPart (X:=X) 1 a_v * degPart (X:=X) m a_u := by
            rw [map_sub, degPart_mul_of_mem_fil ha_u ha_v]
            have h2 : degPart (X:=X) (m+1) (a_v * a_u)
                = degPart (X:=X) 1 a_v * degPart (X:=X) m a_u := by
              have hh := degPart_mul_of_mem_fil (p := 1) (q := m) ha_v ha_u
              rwa [show 1 + m = m + 1 from by omega] at hh
            rw [h2]
          have hA : degPart (X:=X) m a_u ∈ nestedSpan (X:=X) m :=
            ih (by omega) N (by omega) u hu a_u ha_u ha_ueq
          have hW : degPart (X:=X) 1 a_v ∈ nestedSpan (X:=X) 1 :=
            wordSpan_one_le_nestedSpan (degPart_mem_wordSpan 1 a_v)
          have hfin := nestedSpan_bracket_le hA hW
          rw [show degPart (X:=X) (m+1) a
              = degPart (X:=X) (m+1) (a_u * a_v - a_v * a_u) from by
            rw [map_sub, sub_eq_zero] at hdiff_deg; exact hdiff_deg, hc_deg]
          exact hfin
        · -- `z = 1`
          intro a ha haeq
          have hmem : a ∈ fil X N := by
            rw [← Ideal.Quotient.eq_zero_iff_mem, haeq, magLead_one]
          have h0 : degPart (X:=X) (m+1) a = 0 := degPart_eq_zero_of_mem_fil hmem (by omega)
          rw [h0]; exact Submodule.zero_mem _
        · -- product
          intro z1 z2 hz1 hz2 ih1 ih2 a ha haeq
          have hz1' : z1 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := hmem_of z1 hz1
          have hz2' : z2 ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := hmem_of z2 hz2
          obtain ⟨b1, hb1, hb1eq⟩ := (Ideal.mem_map_iff_of_surjective _
            Ideal.Quotient.mk_surjective).1 (magLead_mem_filq N (m+1) (by omega) (by omega) hz1')
          obtain ⟨b2, hb2, hb2eq⟩ := (Ideal.mem_map_iff_of_surjective _
            Ideal.Quotient.mk_surjective).1 (magLead_mem_filq N (m+1) (by omega) (by omega) hz2')
          have hprod : magLead N (z1 * z2)
              = magLead N z1 + magLead N z2 + magLead N z1 * magLead N z2 := by
            unfold magLead
            rw [map_mul, Units.val_mul]
            noncomm_ring
          have hdiff : a - (b1 + b2 + b1 * b2) ∈ fil X N := by
            rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, map_add, map_mul,
              haeq, hprod, hb1eq, hb2eq]
            abel
          have hmain : degPart (X:=X) (m+1) a
              = degPart (X:=X) (m+1) (b1 + b2 + b1 * b2) := by
            have h0 : degPart (X:=X) (m+1) (a - (b1 + b2 + b1 * b2)) = 0 :=
              degPart_eq_zero_of_mem_fil hdiff (by omega)
            rw [map_sub, sub_eq_zero] at h0
            exact h0
          have hzero : degPart (X:=X) (m+1) (b1 * b2) = 0 :=
            degPart_eq_zero_of_mem_fil
              (fil_mul_le X (m+1) (m+1) (Ideal.mul_mem_mul hb1 hb2)) (by omega)
          rw [hmain, map_add, map_add, hzero, add_zero]
          exact Submodule.add_mem _ (ih1 b1 hb1 hb1eq) (ih2 b2 hb2 hb2eq)
        · -- inverse
          intro z hz ihz a ha haeq
          have hz' : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries m := hmem_of z hz
          obtain ⟨b, hb, hbeq⟩ := (Ideal.mem_map_iff_of_surjective _
            Ideal.Quotient.mk_surjective).1 (magLead_mem_filq N (m+1) (by omega) (by omega) hz')
          have hhb : degPart (X:=X) (m+1) b ∈ nestedSpan (X:=X) (m+1) := ihz b hb hbeq
          have hrel : magLead N z⁻¹ + magLead N z + magLead N z⁻¹ * magLead N z = 0 := by
            have h1 : (1 + magLead N z⁻¹) * (1 + magLead N z) = 1 := by
              have hU : (1 + magLead N z⁻¹)
                  = ((magnus X N z⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) := by
                unfold magLead; noncomm_ring
              have hV : (1 + magLead N z)
                  = ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) := by
                unfold magLead; noncomm_ring
              rw [hU, hV, ← Units.val_mul, map_inv, inv_mul_cancel, Units.val_one]
            have h2 : (1 + magLead N z⁻¹) * (1 + magLead N z) - 1
                = magLead N z⁻¹ + magLead N z + magLead N z⁻¹ * magLead N z := by noncomm_ring
            rw [h1, sub_self] at h2
            exact h2.symm
          have hsum : Ideal.Quotient.mk (fil X N) (a + b) ∈ filq X N (m + 1 + 1) := by
            have heq : Ideal.Quotient.mk (fil X N) (a + b)
                = -(Ideal.Quotient.mk (fil X N) a * Ideal.Quotient.mk (fil X N) b) := by
              rw [map_add, haeq, hbeq]
              exact eq_neg_of_add_eq_zero_left hrel
            have hma : Ideal.Quotient.mk (fil X N) a ∈ filq X N (m+1) :=
              Ideal.mem_map_of_mem (Ideal.Quotient.mk (fil X N)) ha
            have hmb : Ideal.Quotient.mk (fil X N) b ∈ filq X N (m+1) :=
              Ideal.mem_map_of_mem (Ideal.Quotient.mk (fil X N)) hb
            have hprod : Ideal.Quotient.mk (fil X N) a * Ideal.Quotient.mk (fil X N) b
                ∈ filq X N ((m+1) + (m+1)) := mul_mem_filq X N (m+1) (m+1) hma hmb
            have hneg : -(Ideal.Quotient.mk (fil X N) a * Ideal.Quotient.mk (fil X N) b)
                ∈ filq X N (m + 1 + 1) :=
              filq_antitone X N (show m + 1 + 1 ≤ (m+1) + (m+1) from by omega) (neg_mem hprod)
            rw [heq]
            exact hneg
          obtain ⟨d, hd, hdeq⟩ := (Ideal.mem_map_iff_of_surjective _
            Ideal.Quotient.mk_surjective).1 hsum
          have hab_zero : degPart (X:=X) (m+1) (a + b) = 0 := by
            have h2 : (a + b) - d ∈ fil X N := by
              rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hdeq, sub_self]
            have h3 : degPart (X:=X) (m+1) ((a + b) - d) = 0 :=
              degPart_eq_zero_of_mem_fil h2 (by omega)
            rw [map_sub, sub_eq_zero] at h3
            rw [h3]
            exact degPart_eq_zero_of_mem_fil hd (by omega)
          rw [map_add] at hab_zero
          rw [eq_neg_of_add_eq_zero_left hab_zero]
          exact neg_mem hhb

/-- The Magnus leading term of an element of `γ_j` is the image of an element of the nested span. -/
theorem magLead_mem_nestedImage (X : Type) (j : ℕ) (hj : 1 ≤ j) (z : FreeGroup X)
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    ∃ a ∈ nestedSpan (X := X) j,
      Ideal.Quotient.mk (fil X (j + 1)) a = magLead (j + 1) z := by
  have hmem : magLead (j + 1) z ∈ filq X (j + 1) j :=
    magLead_mem_filq (j + 1) j hj (by omega) hz
  obtain ⟨a₀, ha₀, ha₀eq⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hmem
  refine ⟨degPart (X:=X) j a₀,
    degPart_mem_nestedSpan_of_magLead j hj (j + 1) le_rfl z hz a₀ ha₀ ha₀eq, ?_⟩
  have hdiff : a₀ - degPart (X:=X) j a₀ ∈ fil X (j + 1) := sub_degPart_mem_fil ha₀
  have hzero : Ideal.Quotient.mk (fil X (j + 1)) (a₀ - degPart (X:=X) j a₀) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hdiff
  rw [map_sub, sub_eq_zero] at hzero
  rw [← ha₀eq]
  exact hzero.symm

end Work.SSGRoute.prop5


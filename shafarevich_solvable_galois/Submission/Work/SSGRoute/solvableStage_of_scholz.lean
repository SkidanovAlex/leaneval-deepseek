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
import Submission.Work.SSGRoute.exists_localLift_outside_T1
import Submission.Work.SSGRoute.stage_global_lifting
import Submission.Work.SSGRoute.stage_local_shrinking_cohomological
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SSGRoute/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared vocabulary: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit — put any new shared definition in your own file). The proved class-field-theory library is available as NK.* (Chebotarev: NK.NUV2.chebotarev_all0 with hFC := NK.CFTLib.fundamentalClassElement; local reciprocity NK.NUV2.kernelCondition_all; existence NK.CFTLib.Existence.classField_exists_primeIndex (unramified only); Hasse–Brauer–Noether NK.GlobalCFTdeep.hbnUnits; NK.KC.localBaseChangeInput_of_kc; NK.HR2.transferStepOnePlace), all axiom-clean. NEVER use Work.HilbertSymbol.GrunwaldWang (false as written). Siblings run in parallel; import them when they land.

# Guidance: Steps 1–2 of the proof of Theorem 15 (SW §5)

Given Scholz solutions at τ at every level, produce at level n a Scholz solution φ_n = (flowGroupMap Φ) ∘ φ_m
that lifts to τ+1 and whose local extensions split over T¹ (`IsSolvableStage`).

**Sketch** (paper pp. 22–26).
1. **Step 1a.** Choose Φ with Prop 6, k = 2, via `Work.CohomologicalShrinking.exists_shrinking_H2_tate`.
   - Take T = ⊕_{v∈T¹∪{∞}} Ind_{D_v}^G 𝔽_p (coinduced modules; instance `coindSMulCommClass`), with
     D_v = image of a decomposition group or ⟨c⟩.
   - The local extension classes lie in H²(φ(D_v), E_m) = H²(G, E_m ⊗ Ind) (Shapiro), because φ_m(D_v)
     ≅ D_v(K/ℚ) by (i). Kill them.
   - Then φ_n = Φ∘φ_m has split local extensions at T¹ ∪ ∞.
   - (i) and (ii) pass to Φ∘φ_m: images of trivial or cyclic totally ramified local groups.
2. **Step 1b/1c.** Local solvability at the remaining places.
   - Unramified places: `SSGRoute.local_tame_lifting`.1 (D/I ≅ Ẑ, Frobenius F).
   - Places ramified in N/K: by (ii) the local group is cyclic totally ramified of order p^a, and a preimage
     in Γ^{τ+1} has order p^{a+ε}, ε ≤ 1. Use `local_tame_lifting`.2 with the μ hypothesis from
     `HasRootsOfUnity` (ℓ splits in K ∋ ζ_{p^{i+1}}).
3. **Step 2.** The global obstruction to lifting φ is φ*(class of Γ^{τ+1} → Γ^τ).
   - Dictionary: `Work.AbsoluteGalois.exists_lift_iff_pullbackCocycle_mem_B2`, and the H²-classification in
     `Work.GroupCohomology`.
   - The obstruction is locally trivial everywhere, so `SSGRoute.sha2_image_of_Hm2` (base ℚ, T = μ_p^∨)
     gives x ∈ Ĥ^{-2}(G, E_m ⊗ T) controlling it.
   - Shrink again with `exists_shrinking_Hm2_tate`, whose `hm2Map` is `Work.Tate.Hm2Map` of
     `(gradedMapLin …).rTensor T`.
   - Naturality: the extension class at level n pulled back along flowGroupMap equals the push-forward of
     the class at level m along E_m → E_n.
4. The composite of the two shrinkings (`OperatorMap.comp`, `exists_operatorMap_of_le`) keeps the Step-1
   splitting: it is inherited by images.

**Assets.** `Prop5Data` from `SSGRoute.prop5Data_exists`; `flowGroupMap`, `flowQuotMap`, `flowNormal`,
`gradedMapLin`, `OperatorMap`; `Work.AbsoluteKummer` (continuous H², finite-level description
`Factorisation.exists_finiteGalois_Z2`).

**Imports.** Interfaces, `SSGRoute.prop5Data_exists`, `SSGRoute.local_tame_lifting`,
`SSGRoute.sha2_image_of_Hm2`, `Submission.Work.AbsoluteGalois.All`,
`Submission.Work.AbsoluteKummer.All`.

Delegate: (1a), (1b/1c), (2), and the naturality of extension classes under flowGroupMap, each as a separate
lemma.
-/

namespace Work.SSGRoute

open SSGRoute
open Work.CohomologicalShrinking

/-! ## The decomposition of `solvableStage_of_scholz` (SW §5, Steps 1–2)

**Status (2026-10-01).**  The proof in this file is complete; the only remaining axiom on its
dependency chain is the Poitou–Tate input of `Work.SSGRoute.stage_global_lifting` (via
`Work.SSGRoute.sha2_image_of_Hm2`, `sha2_dual_control` and the `PT/` lane).  The three delegated
pieces are:

* `SSGRoute.stage_local_shrinking_cohomological` (Step 1a, Prop 6 with `k = 2`): for every level
  `m ≥ m₀` and every Scholz solution `φ` at level `m`, an operator map `Φ₁ : F(m) ⇢ F(n)` such that
  `φM := flowGroupMap Φ₁ ∘ φ` has **split** local extensions at all places of `T¹` *and* at all
  involutions.  Both clauses come from the Shapiro/Proposition-6 argument with
  `T = (⊕_{v∈T¹} Ind_{D_v}^G 𝔽_p) ⊕ Ind_{⟨c⟩}^G 𝔽_p` (the real places are part of the paper's `T`, so
  no separate two-torsion group theory is used — see `AUDIT_p2_two_torsion_atom.lean.md`);
* `SSGRoute.exists_localLift_outside_T1` (Steps 1b/1c, from `local_tame_lifting`): `φM` is locally
  liftable, with *open* kernel, at every finite place outside `T¹`;
* `SSGRoute.stage_global_lifting` (Step 2, `sha2_image_of_Hm2` + `exists_shrinking_Hm2_tate`): at
  level `m₀G` those local data give `Φ₂ : F(m₀G) ⇢ F(n)` and a continuous lift
  `ψ : G_ℚ →* Γ^{τ+1}_n` of `flowGroupMap Φ₂ ∘ φM`, keeping the `T¹` splitting.

The final solution is `φn = flowGroupMap Φ₂ ∘ φM`; `scholzSolution_comp_flowGroupMap` (proved here)
shows it is Scholz at level `n`, `ψ` is the required lift, and the `T¹`-splitting is the local clause
of `IsSolvableStage`.  Level bookkeeping: the first shrinking has target `m₀G` (not `n`) because
`stage_global_lifting` needs the level-`m` solution itself to be locally trivial at *every* place.

Two glue lemmas are proved in this file: `scholzSolution_comp_flowGroupMap` (Scholz solutions pass to
images under `flowGroupMap`) and `isOpen_comap_subtype` (relative openness), together with
`flowGroupMap_surjective`/`flowQuotMap_surjective` and the cyclicity transfer `isCyclic_map_of_isCyclic`. -/


/-! ## The decomposition of `solvableStage_of_scholz` (SW §5, Steps 1–2)

The proof below is assembled from exactly three delegated lemmas (all in
`Submission/Work/SSGRoute/`), each of which is one of the steps the paper performs, plus two
elementary glue lemmas proved in this file.

**Level bookkeeping.**  The conclusion at level `n` is produced from a Scholz solution at a much
larger level by *shrinking*: an operator map `Φ : F(m) ⇢ F(n)` pushes a solution `φ` at level `m`
to the solution `flowGroupMap Φ ∘ φ` at level `n`.  Two shrinkings are composed:

* `stage_local_shrinking` (Step 1a, Prop 6 with `k = 2`): applied with target level `m₀G`
  (the threshold of the second shrinking), it produces `Φ₁ : F(m₀L) ⇢ F(m₀G)` such that the
  pushed solution `φM = flowGroupMap Φ₁ ∘ φ'` has *split* local extensions at all places of `T¹`
  and at all involutions;
* `stage_local_solvable` (Steps 1b/1c, from `SSGRoute.local_tame_lifting`): for such a `φM`, the
  local extension splits — or at least is liftable — at every finite place outside `T¹`;
* `stage_global_lifting` (Step 2, `sha2_image_of_Hm2` + `exists_shrinking_Hm2_tate`): applied at
  level `m₀G` with target `n`, this yields `Φ₂ : F(m₀G) ⇢ F(n)` together with a global lift
  `ψ : G_ℚ → Γ^{τ+1}_n` of `flowGroupMap Φ₂ ∘ φM` whose kernel is open, and it keeps the `T¹`
  splitting.  (Its hypotheses are exactly the local data produced by the previous two steps.)

The final solution is `φn = flowGroupMap Φ₂ ∘ φM`, which is Scholz at level `n` by
`scholzSolution_comp_flowGroupMap`; the lift `ψ` and the `T¹`-splitting then give
`IsSolvableStage p K n i j` verbatim.

**Why the *first* shrinking must have target `m₀G` (and not `n`).**  Step 2 needs the level-`m`
solution itself to be locally trivial at *every* place (that is the hypothesis of
`sha2_image_of_Hm2`); a failing local extension at a place of `T¹` is repaired only by the
shrinking, which kills the local extension *class at the source level*.  Hence the first
shrinking is applied at level `m₀L` with target `m₀G`: the killed classes are the level-`m₀L`
ones, so the induced level-`m₀G` local extensions split.
-/


/-! ## Glue lemmas for the rank change `F(m) ⇢ F(n)`

The whole induction step of Theorem 15 produces, at the level `n`, a solution of the `τ`-problem
out of a solution at a larger level `m ≥ n` by pushing forward along a surjective `G`-operator
homomorphism `Φ : F(m) ⇢ F(n)` (Schmidt–Wingberg's "shrinking").  This section records the two
elementary facts about that push-forward that the rest of the chapter needs. -/

section Glue

variable {p : ℕ} {G : Type*} [Group G]

/-- The image of a cyclic subgroup under a homomorphism is cyclic. -/
theorem isCyclic_map_of_isCyclic {N P : Type*} [Group N] [Group P] (f : N →* P) (H : Subgroup N)
    (h : IsCyclic ↥H) : IsCyclic ↥(Subgroup.map f H) := by
  let F : ↥H →* ↥(Subgroup.map f H) :=
    { toFun := fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.1 b.1) }
  have hsurj : Function.Surjective F := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact isCyclic_of_surjective F hsurj

/-- **Relative openness of the preimage of an open subgroup.**  If `K ≤ G` is an open subgroup of
the topological group `G` and `H ≤ G` is any subgroup, then `K ∩ H` is open in the subspace
topology on `H`.  This is the form in which the openness of the kernel of a *local* lift
(`l : D_A →* Γ^{τ+1}` with `ker(φ|D_A) ≤ ker l`) is inherited from the openness of `ker φ`. -/
theorem isOpen_comap_subtype {H K : Subgroup SSGRoute.GalQ} (hK : IsOpen (K : Set SSGRoute.GalQ)) :
    IsOpen ((K.comap H.subtype : Subgroup ↥H) : Set ↥H) := by
  have h : (K.comap H.subtype : Set ↥H) = H.subtype ⁻¹' (K : Set SSGRoute.GalQ) := rfl
  rw [h]
  exact hK.preimage continuous_subtype_val

/-- `flowQuotMap` is surjective (it is induced by a surjective operator map). -/
theorem flowQuotMap_surjective {m n : ℕ} (i j : ℕ) (Φ : OperatorMap G m n) :
    Function.Surjective (flowQuotMap p G i j Φ) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨z, hz⟩ := Φ.surjective x.1
    refine ⟨QuotientGroup.mk' _ ⟨z, Subgroup.mem_top z⟩, ?_⟩
    rw [flowQuotMap_mk]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext hz)

/-- `flowGroupMap` is surjective. -/
theorem flowGroupMap_surjective {m n : ℕ} (i j : ℕ) (Φ : OperatorMap G m n) :
    Function.Surjective (flowGroupMap p G i j Φ) := by
  intro γ
  obtain ⟨x, hx⟩ := flowQuotMap_surjective (p := p) i j Φ γ.left
  have key : flowGroupMap p G i j Φ (SemidirectProduct.mk x γ.right)
      = SemidirectProduct.mk ((flowQuotMap p G i j Φ) x) γ.right := by
    rw [flowGroupMap]
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.map_left]
    · rw [SemidirectProduct.map_right]; rfl
  exact ⟨SemidirectProduct.mk x γ.right, by rw [key, hx]⟩

end Glue

/-- **Scholz solutions are stable under the rank change `F(m) ⇢ F(n)`.**  A surjective
`G`-operator homomorphism `Φ : F(m) ⇢ F(n)` induces `flowGroupMap Φ : Γ_m^τ →* Γ_n^τ`, and the
push-forward of a Scholz solution at level `m` is a Scholz solution at level `n`:

* surjectivity and open kernel are inherited (the kernel can only grow);
* `flowQuot` is natural (`flowQuot_flowGroupMap`);
* conditions (i), (ii) of Theorem 15 are inherited by images: `φ σ = 1` implies
  `(flowGroupMap Φ ∘ φ) σ = 1`, the image of a cyclic group is cyclic, and the "elements are hit by
  inertia" condition is preserved by applying `flowGroupMap Φ`. -/
theorem scholzSolution_comp_flowGroupMap (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    {m n i j : ℕ} (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ) :
    SSGRoute.IsScholzSolution p K n i j ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) := by
  obtain ⟨hflow, hsch⟩ := hφ
  obtain ⟨hsurj, hopen, hres⟩ := hflow
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (flowGroupMap_surjective (p := p) i j Φ).comp hsurj
  · refine Subgroup.isOpen_mono ?_ hopen
    intro σ hσ
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ ⊢
    rw [hσ, map_one]
  · intro σ
    rw [MonoidHom.comp_apply, flowQuot_flowGroupMap]
    exact hres σ
  · intro A hA σ hσ hσK
    rw [MonoidHom.comp_apply, hsch.1 A hA σ hσ hσK, map_one]
  · intro c hc hcK
    rw [MonoidHom.comp_apply, hsch.2.1 c hc hcK, map_one]
  · intro A hA h
    obtain ⟨σ, hσ, hσK, hne⟩ := h
    have hne' : φ σ ≠ 1 := fun hc => hne (by rw [MonoidHom.comp_apply, hc, map_one])
    obtain ⟨h1, h2, h3⟩ := hsch.2.2 A hA ⟨σ, hσ, hσK, hne'⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [← Subgroup.map_map (K := SSGRoute.decomp ℚ A) (f := φ)
        (g := flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ)]
      exact isCyclic_map_of_isCyclic _ _ h2
    · intro σ' hσ'
      obtain ⟨τ, hτ, hτφ⟩ := h3 σ' hσ'
      exact ⟨τ, hτ, by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hτφ]⟩

/-- **`IsSolvableStage` from a lift that kills the `T¹`-part of the kernel.**  This isolates the
final, purely group-theoretic step of "Steps 1–2": once one has a Scholz solution `φ` at level `n`
together with a (continuous, not necessarily proper) lift `ψ` to `τ + 1` whose kernel contains the
local kernels `ker(φ) ∩ D_A` for the places `A` of `T¹`, the local groups `l_A := ψ|_{D_A}` supply
the local splittings required by `IsSolvableStage`. -/
theorem isSolvableStage_of_lift (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hφ : SSGRoute.IsScholzSolution p K n i j φ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψ : SSGRoute.LiftsFlow ψ φ) (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ))
    (hloc : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1 → ψ σ = 1) :
    SSGRoute.IsSolvableStage p K n i j := by
  refine ⟨φ, ψ, hφ, hψ, hopen, ?_⟩
  intro A hA
  exact ⟨ψ.comp (Subgroup.subtype (SSGRoute.decomp ℚ A)),
    fun σ => hψ σ.1,
    fun σ hσ => hloc A hA σ.1 σ.2 hσ⟩

open SSGRoute
theorem solvableStage_of_scholz (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hIH : ∀ n : ℕ, 1 ≤ n →
      ∃ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j,
        SSGRoute.IsScholzSolution p K n i j φ)
    (n : ℕ) (hn : 1 ≤ n) :
    SSGRoute.IsSolvableStage p K n i j := by
  -- **Step 2** at the final level `n`: the threshold `m₀G` of the second (global) shrinking.
  obtain ⟨m₀G, hm₀G, hG⟩ := stage_global_lifting p K i j hj hji hμ n hn
  have hm₀G1 : 1 ≤ m₀G := le_trans hn hm₀G
  -- **Step 1a** with target level `m₀G`: the first (local) shrinking, obtained by the
  -- Shapiro/Proposition-6 argument for *both* clauses (the real places are in the paper's `T`).
  obtain ⟨m₀L, hm₀L, hL⟩ := stage_local_shrinking_cohomological p K i j hj hji hμ m₀G hm₀G1
  have hm₀L1 : 1 ≤ m₀L := le_trans hm₀G1 hm₀L
  -- A Scholz solution at level `m₀L` (the induction hypothesis), pushed down to level `m₀G`.
  obtain ⟨φ', hφ'⟩ := hIH m₀L hm₀L1
  obtain ⟨Φ₁, hΦ₁T1, hΦ₁inv⟩ := hL m₀L le_rfl φ' hφ'
  set φM : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m₀G i j :=
    (Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ₁).comp φ' with hφM
  have hφMscholz : SSGRoute.IsScholzSolution p K m₀G i j φM :=
    scholzSolution_comp_flowGroupMap p K Φ₁ φ' hφ'
  have hφMopen : IsOpen (φM.ker : Set SSGRoute.GalQ) := hφMscholz.1.2.1
  -- **Step 1b/1c**: local solvability, with *open* kernel, at the places outside `T¹`.
  have hOther : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      ¬ SSGRoute.IsT1Place p K A →
      ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m₀G
            (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φM σ)) ∧
        IsOpen (l.ker : Set ↥(SSGRoute.decomp ℚ A)) :=
    exists_localLift_outside_T1 p K i j hj hji hμ m₀G φM hφMscholz
  -- **Step 1a** again: at the places of `T¹` the shrinking gives the local *splitting*; the
  -- openness of the kernel follows because `l` factors through `φM` and `ker φM` is open.
  have hT1 : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m₀G
            (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φM σ)) ∧
        IsOpen (l.ker : Set ↥(SSGRoute.decomp ℚ A)) ∧
        (∀ σ : ↥(SSGRoute.decomp ℚ A), φM σ = 1 → l σ = 1) := by
    intro A hA
    obtain ⟨l, hl₁, hl₂⟩ := hΦ₁T1 A hA
    exact ⟨l, hl₁, Subgroup.isOpen_mono (fun σ hσ => hl₂ σ hσ)
      (isOpen_comap_subtype (H := SSGRoute.decomp ℚ A) hφMopen), hl₂⟩
  -- The same at the real places.
  have hInv : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      ∃ l : ↥(Subgroup.zpowers c) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m₀G
            (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ σ : ↥(Subgroup.zpowers c), SSGRoute.LiftsFlowAt (l σ) (φM σ)) ∧
        IsOpen (l.ker : Set ↥(Subgroup.zpowers c)) := by
    intro c hc
    obtain ⟨l, hl₁, hl₂⟩ := hΦ₁inv c hc
    exact ⟨l, hl₁, Subgroup.isOpen_mono (fun σ hσ => hl₂ σ hσ)
      (isOpen_comap_subtype (H := Subgroup.zpowers c) hφMopen)⟩
  -- **Step 2**: the second shrinking produces the lift at level `n`.
  obtain ⟨Φ₂, ψ, hψ, hopen, hlocT1⟩ := hG m₀G le_rfl φM hφMscholz hOther hT1 hInv
  exact ⟨(Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ₂).comp φM, ψ,
    scholzSolution_comp_flowGroupMap p K Φ₂ φM hφMscholz, hψ, hopen, hlocT1⟩

end Work.SSGRoute

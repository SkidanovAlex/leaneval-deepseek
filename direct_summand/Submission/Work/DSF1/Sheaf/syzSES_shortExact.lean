import Mathlib
import Submission.Work.DSF1.Sheaf.AcyclicToolkit

/-!
# Short exactness of the syzygy short complex

For a cochain complex `K` indexed by `ℕ` whose homology in degree `n + 1` vanishes, the short
complex
`0 → syz K n → K.X n → syz K (n + 1) → 0`
is short exact (the `syzSES` of `Submission.Work.DSF1.Sheaf.AcyclicToolkit`).

The three ingredients are:

* the first map `syzIncl K n = kernel.ι (K.d n (n+1))` is a monomorphism;
* the second map `syzProj K n`, the corestriction of `K.d n (n+1)` to `syz K (n+1) =
  ker (K.d (n+1) (n+2))`, is an epimorphism exactly when the homology in degree `n+1`
  vanishes — that is the hypothesis `h`;
* the pair is exact at the middle term, with no hypothesis on `K` at all: since
  `syzProj K n ≫ syzIncl K (n+1) = K.d n (n+1)` and `syzIncl K (n+1)` is a monomorphism, a
  kernel of `syzProj K n` is the same thing as a kernel of `K.d n (n+1)`, and the latter is
  exhibited by `syzIncl K n`.
-/

set_option linter.style.haveILetI false

namespace Work.DSF1.Sheaf

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The inclusion `syzIncl K n = kernel.ι (K.d n (n+1))` of the `n`-th syzygy of `K` is a
monomorphism. -/
lemma mono_syzIncl (K : CochainComplex C ℕ) (n : ℕ) : Mono (syzIncl K n) := by
  change Mono (Limits.kernel.ι (K.d n (n+1)))
  infer_instance

/-- If the homology of `K` in degree `n + 1` vanishes, then the projection `syzProj K n` onto
the `(n+1)`-st syzygy is an epimorphism: `syzProj K n` is the factorisation of the differential
`K.d n (n+1)` through the kernel of `K.d (n+1) (n+2)`, and the vanishing of `H^{n+1}` says
exactly that this factorisation is surjective. -/
lemma epi_syzProj_of_isZero_homology (K : CochainComplex C ℕ)
    [∀ i : ℕ, HomologicalComplex.HasHomology K i] (n : ℕ)
    (h : IsZero (K.homology (n+1))) : Epi (syzProj K n) := by
  have hExactAt : K.ExactAt (n+1) := (HomologicalComplex.exactAt_iff_isZero_homology K (n+1)).2 h
  have hS : (K.sc' n (n+1) (n+2)).Exact :=
    (HomologicalComplex.exactAt_iff' K n (n+1) (n+2)
      (ComplexShape.prev_eq' _ (ComplexShape.up_mk n (n+1) rfl))
      (ComplexShape.next_eq' _ (ComplexShape.up_mk (n+1) (n+2) rfl))).1 hExactAt
  have hS' : (ShortComplex.mk (K.d n (n+1)) (K.d (n+1) (n+2))
      (HomologicalComplex.d_comp_d K n (n+1) (n+2))).Exact := hS
  exact ShortComplex.Exact.epi_kernelLift hS'

/-- The syzygy short complex `0 → syz K n → K.X n → syz K (n+1) → 0` is exact at its middle
term, for an arbitrary complex `K`: the corestriction `syzProj K n` of `K.d n (n+1)` to
`syz K (n+1)` has the same kernels as `K.d n (n+1)` (as `syzProj K n ≫ syzIncl K (n+1) =
K.d n (n+1)` with `syzIncl K (n+1)` a mono), and `syzIncl K n` is a kernel of `K.d n (n+1)`. -/
lemma exact_syzSES (K : CochainComplex C ℕ) (n : ℕ) : (syzSES K n).Exact := by
  haveI hm : Mono (syzIncl K (n+1)) := mono_syzIncl K (n+1)
  have hzero : syzIncl K n ≫ syzProj K n = 0 := (syzSES K n).zero
  have hkf : Limits.kernel.ι (K.d n (n+1)) ≫ syzProj K n = 0 := by
    rw [← cancel_mono (syzIncl K (n+1))]
    simp only [Category.assoc, syzProj_comp_syzIncl, Limits.kernel.condition, zero_comp]
  have hker : IsLimit (KernelFork.ofι (syzIncl K n) hzero) :=
    Limits.isKernelOfComp (f := syzProj K n) (g := syzIncl K (n+1)) (h := K.d n (n+1))
      (kernelIsKernel (K.d n (n+1))) hkf (syzProj_comp_syzIncl K n)
  exact ShortComplex.exact_of_f_is_kernel _ hker

theorem syzSES_shortExact {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    (K : CochainComplex C ℕ) [∀ i : ℕ, HomologicalComplex.HasHomology K i] (n : ℕ)
    (h : CategoryTheory.Limits.IsZero (K.homology (n+1))) :
    (Work.DSF1.Sheaf.syzSES K n).ShortExact := by
  refine ShortComplex.ShortExact.mk' (exact_syzSES K n) (mono_syzIncl K n) ?_
  exact epi_syzProj_of_isZero_homology K n h

end Work.DSF1.Sheaf

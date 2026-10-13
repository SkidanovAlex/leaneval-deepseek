/-
# The Galerkin span under `UnifIP` : orthonormality and Bessel's inequality

`Work.FTS.Galerkin.IsIPOrthonormal IP φ` — the *usable* form of the orthonormality of a Galerkin
basis, `IP (galFun φ d) (galFun φ c) = ∑ₖ dₖcₖ` — is derived in
`Submission/Work/FTS/Galerkin/OrdBridge.lean` from the raw orthonormality only for an inner
product `Work.FTS.Galerkin.IsH4Inner`, whose bilinearity is *unrestricted*.  The corrected inner
product of the a-priori chapter is N2's `Work.FTS.Nonlin.UnifIP`, whose bilinearity
(`add_fst`, `smul_fst`) is restricted to the interior class `RegQ α 4`; the derivation therefore
has to keep track of the class of every partial combination.  This module does that:

* `regQ_phi` — every test function of a `GalBasis` lies in `RegQ α 4` (from `GalBasis.cls` at
  `n = 1` and `regQ_mono`);
* `ip_galFun_phi` — coefficient extraction: `IP α (galFun φ d) (φ k) = d k`;
* `isIPOrthonormal_of_galBasis` — **the orthonormality of the Galerkin span** under `UnifIP`;
* `bessel_galBasis` — **Bessel's inequality** `∑ₖ (IP α g₀ (φ k))² ≤ IP α g₀ g₀`, which is the
  content of N5's `hInit` (design §4 L-N5.6).

Everything rests on the closure of `RegQ` under finite linear combinations
(`Submission.Work.FTS.OpenPkg.AprioriOpen.RegQApi`).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.Galerkin.Hilbert
import Submission.Work.FTS.OpenPkg.AprioriOpen.RegQApiOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.AprioriOpen

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Bilinearity of `UnifIP` in its second argument, on the class `RegQ` -/

/-- Additivity of `UnifIP` in its second argument, on `RegQ`. -/
theorem ip_add_snd {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {f g₁ g₂ : Fn} (hf : RegQ α 4 f) (h1 : RegQ α 4 g₁) (h2 : RegQ α 4 g₂) :
    IP α f (fun z θ => g₁ z θ + g₂ z θ) = IP α f g₁ + IP α f g₂ := by
  rw [show IP α f (fun z θ => g₁ z θ + g₂ z θ) = IP α f (g₁ + g₂) from rfl,
    hIP.symm α f (g₁ + g₂), hIP.add_fst α hα g₁ g₂ f h1 h2 hf,
    hIP.symm α g₁ f, hIP.symm α g₂ f]

/-- Scalar homogeneity of `UnifIP` in its second argument, on `RegQ`. -/
theorem ip_smul_snd {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    (c : ℝ) {f g : Fn} (hf : RegQ α 4 f) (hg : RegQ α 4 g) :
    IP α f (fun z θ => c * g z θ) = c * IP α f g := by
  rw [hIP.symm α f (fun z θ => c * g z θ), hIP.smul_fst α hα c g f hg hf, hIP.symm α g f]

/-- Negation of `UnifIP` in its first argument, on `RegQ`. -/
theorem ip_neg_fst {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {f g : Fn} (hf : RegQ α 4 f) (hg : RegQ α 4 g) :
    IP α (fun z θ => -f z θ) g = -IP α f g := by
  have h := hIP.smul_fst α hα (-1) f g hf hg
  simpa using h

/-- Negation of `UnifIP` in its second argument, on `RegQ`. -/
theorem ip_neg_snd {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {f g : Fn} (hf : RegQ α 4 f) (hg : RegQ α 4 g) :
    IP α f (fun z θ => -g z θ) = -IP α f g := by
  have h := ip_smul_snd hIP hα (-1) hf hg
  simpa using h

/-- **The quadratic expansion of `IP` on a difference**: `|f - g|²_IP = |f|²_IP - 2(f,g)_IP +
|g|²_IP`. -/
theorem ip_sub_self {α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {f g : Fn} (hf : RegQ α 4 f) (hg : RegQ α 4 g) :
    IP α (fun z θ => f z θ - g z θ) (fun z θ => f z θ - g z θ)
      = IP α f f - 2 * IP α f g + IP α g g := by
  have hgn : RegQ α 4 (fun z θ => -g z θ) := regQ_neg hg
  have hsum : RegQ α 4 (fun z θ => f z θ + (-g z θ)) := regQ_add hf hgn
  have hEq : (fun z θ => f z θ - g z θ) = (fun z θ => f z θ + (-g z θ)) := rfl
  rw [hEq]
  rw [show (fun z θ => f z θ + (-g z θ)) = (f + fun z θ => -g z θ) from rfl]
  rw [hIP.add_fst α hα f (fun z θ => -g z θ) (f + fun z θ => -g z θ) hf hgn hsum,
    show (f + fun z θ => -g z θ) = fun z θ => f z θ + (-g z θ) from rfl,
    ip_add_snd hIP hα hf hf hgn, ip_add_snd hIP hα hgn hf hgn,
    ip_neg_snd hIP hα hf hg,
    show IP α (fun z θ => -g z θ) f = -IP α f g from by
      rw [ip_neg_fst hIP hα hg hf, hIP.symm α g f],
    show IP α (fun z θ => -g z θ) (fun z θ => -g z θ) = IP α g g from by
      rw [ip_neg_fst hIP hα hg hgn, ip_neg_snd hIP hα hg hg]; ring]
  ring

/-! ## The Galerkin span -/

/-- **Every test function of a `GalBasis` is in the interior class `RegQ α 4`.** -/
theorem regQ_phi {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ} {φ : ℕ → Fn}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂) (hφ : GalBasis α IP φ)
    (i : ℕ) : RegQ α 4 (φ i) := by
  have h := hφ.cls (i + 1) (Pi.single ⟨i, Nat.lt_succ_self i⟩ (1 : ℝ))
  have h2 : galFun φ (Pi.single ⟨i, Nat.lt_succ_self i⟩ (1 : ℝ)) = φ i :=
    Work.FTS.Galerkin.galFun_single φ ⟨i, Nat.lt_succ_self i⟩
  rw [h2] at h
  exact regQ_mono (k := 6) (by norm_num) h.reg

/-- **Coefficient extraction**: the `k`-th coefficient of a Galerkin combination is its pairing
with the `k`-th test function, under the restricted bilinearity of `UnifIP`. -/
theorem ip_galFun_phi {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ} {φ : ℕ → Fn}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂) (hφ : GalBasis α IP φ)
    (n : ℕ) (d : Fin n → ℝ) (k : Fin n) : IP α (galFun φ d) (φ (k : ℕ)) = d k := by
  have hphi : ∀ i : ℕ, RegQ α 4 (φ i) := regQ_phi hIP hα hφ
  have key : ∀ s : Finset (Fin n),
      IP α (fun z θ => ∑ i ∈ s, d i * φ (i : ℕ) z θ) (φ (k : ℕ))
        = ∑ i ∈ s, d i * (if i = k then (1 : ℝ) else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hz := hIP.smul_fst α hα (0 : ℝ) (0 : Fn) (φ (k : ℕ))
          (regQ_zero α 4) (hphi (k : ℕ))
        simpa using hz
    | insert a s' ha ih =>
        have hsplit : (fun z θ => ∑ i ∈ insert a s', d i * φ (i : ℕ) z θ)
            = (fun z θ => d a * φ (a : ℕ) z θ)
              + (fun z θ => ∑ i ∈ s', d i * φ (i : ℕ) z θ) := by
          funext z θ
          rw [Finset.sum_insert ha]
          rfl
        rw [hsplit]
        have h1 : RegQ α 4 (fun z θ => d a * φ (a : ℕ) z θ) := regQ_smul (d a) (hphi (a : ℕ))
        have h2 : RegQ α 4 (fun z θ => ∑ i ∈ s', d i * φ (i : ℕ) z θ) :=
          regQ_finset_sum s' d (fun i => φ i) (fun i _ => hphi i)
        rw [hIP.add_fst α hα _ _ _ h1 h2 (hphi (k : ℕ)),
          hIP.smul_fst α hα (d a) (φ (a : ℕ)) (φ (k : ℕ)) (hphi (a : ℕ)) (hphi (k : ℕ)),
          hφ.orth a k, ih, Finset.sum_insert ha]
        simp only [Fin.ext_iff]
  have hmain : IP α (galFun φ d) (φ (k : ℕ))
      = ∑ i : Fin n, d i * (if i = k then (1 : ℝ) else 0) := by
    have h := key (Finset.univ : Finset (Fin n))
    rw [show IP α (galFun φ d) (φ (k : ℕ))
        = IP α (fun z θ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
            d i * φ (i : ℕ) z θ) (φ (k : ℕ)) from rfl]
    exact h
  rw [hmain, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **The Galerkin span is `UnifIP`-orthonormal**: for a `GalBasis`, the pairing of two Galerkin
combinations is the Euclidean pairing of their coefficient vectors.  This is the counterpart, in
the corrected class-restricted vocabulary, of `Work.FTS.Galerkin.isIPOrthonormal_of_orth`. -/
theorem isIPOrthonormal_of_galBasis {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    {φ : ℕ → Fn} (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hφ : GalBasis α IP φ) : Work.FTS.Galerkin.IsIPOrthonormal (IP α) φ := by
  have hphi : ∀ i : ℕ, RegQ α 4 (φ i) := regQ_phi hIP hα hφ
  intro n d c
  have hrd : RegQ α 4 (galFun φ d) := regQ_mono (k := 6) (by norm_num) (hφ.cls n d).reg
  have key : ∀ s : Finset (Fin n),
      IP α (galFun φ d) (fun z θ => ∑ i ∈ s, c i * φ (i : ℕ) z θ)
        = ∑ i ∈ s, c i * (IP α (galFun φ d) (φ (i : ℕ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hz := ip_smul_snd hIP hα (0 : ℝ) hrd (regQ_zero α 4)
        simpa using hz
    | insert a s' ha ih =>
        have hsplit : (fun z θ => ∑ i ∈ insert a s', c i * φ (i : ℕ) z θ)
            = fun z θ => c a * φ (a : ℕ) z θ
              + (∑ i ∈ s', c i * φ (i : ℕ) z θ) := by
          funext z θ
          rw [Finset.sum_insert ha]
        rw [hsplit]
        have h1 : RegQ α 4 (fun z θ => c a * φ (a : ℕ) z θ) := regQ_smul (c a) (hphi (a : ℕ))
        have h2 : RegQ α 4 (fun z θ => ∑ i ∈ s', c i * φ (i : ℕ) z θ) :=
          regQ_finset_sum s' c (fun i => φ i) (fun i _ => hphi i)
        rw [ip_add_snd hIP hα hrd h1 h2,
          ip_smul_snd hIP hα (c a) hrd (hphi (a : ℕ)), ih, Finset.sum_insert ha]
  have hmain : IP α (galFun φ d) (galFun φ c)
      = ∑ i : Fin n, c i * (IP α (galFun φ d) (φ (i : ℕ))) := by
    have h := key (Finset.univ : Finset (Fin n))
    rw [show IP α (galFun φ d) (galFun φ c)
        = IP α (galFun φ d) (fun z θ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
            c i * φ (i : ℕ) z θ) from rfl]
    exact h
  rw [hmain]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ip_galFun_phi hIP hα hφ n d i]
  ring

/-- **Bessel's inequality for the Galerkin projection** (design §4 L-N5.6): the coefficients of the
projection of `g₀` onto the Galerkin span have `ℓ²`-norm bounded by `IP α g₀ g₀`. -/
theorem bessel_galBasis {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ} {φ : ℕ → Fn}
    {g₀ : Fn} (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hφ : GalBasis α IP φ) (hg : RegQ α 4 g₀) (n : ℕ) :
    ∑ k : Fin n, (IP α g₀ (φ (k : ℕ))) ^ 2 ≤ IP α g₀ g₀ := by
  classical
  have hphi : ∀ i : ℕ, RegQ α 4 (φ i) := regQ_phi hIP hα hφ
  set c : Fin n → ℝ := fun k => IP α g₀ (φ (k : ℕ)) with hc
  have hS : RegQ α 4 (galFun φ c) := regQ_mono (k := 6) (by norm_num) (hφ.cls n c).reg
  have hSS : RegQ α 4 (fun z θ => g₀ z θ - galFun φ c z θ) := regQ_sub hg hS
  -- the second-argument expansion of `IP g₀ (-)`
  have key : ∀ s : Finset (Fin n),
      IP α g₀ (fun z θ => ∑ i ∈ s, c i * φ (i : ℕ) z θ)
        = ∑ i ∈ s, c i * (IP α g₀ (φ (i : ℕ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hz := ip_smul_snd hIP hα (0 : ℝ) hg (regQ_zero α 4)
        simpa using hz
    | insert a s' ha ih =>
        have hsplit : (fun z θ => ∑ i ∈ insert a s', c i * φ (i : ℕ) z θ)
            = fun z θ => c a * φ (a : ℕ) z θ
              + (∑ i ∈ s', c i * φ (i : ℕ) z θ) := by
          funext z θ
          rw [Finset.sum_insert ha]
        rw [hsplit]
        have h1 : RegQ α 4 (fun z θ => c a * φ (a : ℕ) z θ) := regQ_smul (c a) (hphi (a : ℕ))
        have h2 : RegQ α 4 (fun z θ => ∑ i ∈ s', c i * φ (i : ℕ) z θ) :=
          regQ_finset_sum s' c (fun i => φ i) (fun i _ => hphi i)
        rw [ip_add_snd hIP hα hg h1 h2, ip_smul_snd hIP hα (c a) hg (hphi (a : ℕ)), ih,
          Finset.sum_insert ha]
  have hexp1 : IP α g₀ (galFun φ c) = ∑ k : Fin n, (c k) ^ 2 := by
    have h := key (Finset.univ : Finset (Fin n))
    rw [show IP α g₀ (galFun φ c)
        = IP α g₀ (fun z θ => ∑ i ∈ (Finset.univ : Finset (Fin n)),
            c i * φ (i : ℕ) z θ) from rfl]
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc]
    ring
  have hexp2 : IP α (galFun φ c) (galFun φ c) = ∑ k : Fin n, (c k) ^ 2 := by
    rw [(isIPOrthonormal_of_galBasis hIP hα hφ) n c c]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hnonneg : 0 ≤ IP α (fun z θ => g₀ z θ - galFun φ c z θ)
      (fun z θ => g₀ z θ - galFun φ c z θ) := hIP.nonneg α hα _ hSS
  rw [ip_sub_self hIP hα hg hS, hexp1, hexp2] at hnonneg
  linarith

end Work.FTS.OpenPkg.AprioriOpen

import Mathlib
import Submission.Work.TMComp.Duality.Defs
import Submission.Work.TMComp.Duality.Basic
import Submission.Work.TMComp.Duality.PhaseIndep
import Submission.Work.TMComp.Duality.amoOp_selfAdjoint
import Submission.Work.TMComp.Duality.coordOpStar
import Submission.Work.TMComp.Duality.blockVec_norm
import Submission.Work.TMComp.Duality.two_cos_phase
import Submission.Work.TMC7Core.Scale.spectral_continuity

/-!
# `σ(suspA α λ) ⊆ σ(amoOp α λ 0)`

For irrational `α`, every spectral point of the suspension `suspA α λ` of the almost Mathieu
cocycle is a spectral point of the almost Mathieu operator `amoOp α λ 0` at phase `0`.

The suspension is the direct integral, over the phase `ϑ ∈ ℝ/ℤ`, of the operators `amoOp α λ ϑ`,
and the spectrum of `amoOp α λ ϑ` does not depend on `ϑ` (`amoOp_spectrum_phase`).  The proof
given here is a self-contained Weyl-sequence argument:

* `TMAux.fibVec_suspA_alt` : the twisted partial Fourier transform `fibVec` intertwines
  `suspA α λ` with `amoOp α λ ϑ` (Aubry duality, vector form).  It is proved by reducing to
  basis vectors, where the identity is the elementary trigonometric identity `two_cos_phase`;
  no reindexing of sums is needed.
* `TMAux.fibVec_parseval_zero` : for a vector supported in a box whose side `N` exceeds the
  diameter of its support, the twisted Fourier sums over the `N` phases `j/N` satisfy the
  exact Plancherel identity `Σ_j ‖fibVec (j/N) v‖² = N ‖v‖²`.  It is deduced from the
  orthogonality of the characters, `Σ_j e^{2πi r j/N} = N [N ∣ r]`.
* `TMAux.suspA_selfAdjoint_alt` : `suspA α λ` is self-adjoint, so its spectrum is real.

Given a real `z ∈ σ(suspA α λ)` and `d = dist(z, σ(amoOp α λ 0)) > 0`, the intertwining gives,
for every finitely supported `v` and every `j`,
`d ‖fibVec_{j/N} v‖ ≤ ‖fibVec_{j/N} ((suspA α λ - z) v)‖`; summing the squares over `j` and
applying Plancherel on both sides yields `d ‖v‖ ≤ ‖(suspA α λ - z) v‖`.  Extending by density
contradicts `z ∈ σ(suspA α λ)`.
-/

open LeanEval.Analysis.TenMartini

open scoped ENNReal ComplexConjugate

open Filter Topology

open Work.TMC7Core.Scale

noncomputable section

namespace Work.TMComp.Duality

namespace TMAux

theorem star_ph (α : ℝ) (n : ℤ) : star (ph α n) = ph α (-n) := by
  rw [show star (ph α n) = conj (ph α n) from rfl, conj_ph]

theorem star_s2Sh : star s2Sh = s2Sh' := by
  show s2Sh.adjoint = s2Sh'
  apply coord_ext
  intro f p
  rw [s2Sh, adjoint_coordOp, s2Sh', coordOp_coord,
    show (shiftSnd (1 : ℤ)).symm p = (p.1, p.2 - 1) from rfl]
  simp [sub_eq_add_neg]

theorem star_s2Sh' : star s2Sh' = s2Sh := by
  show s2Sh'.adjoint = s2Sh
  apply coord_ext
  intro f p
  rw [s2Sh', adjoint_coordOp, s2Sh, coordOp_coord,
    show (shiftSnd (-1 : ℤ)).symm p = (p.1, p.2 + 1) from rfl]
  simp [sub_eq_add_neg]

theorem star_coord_s2P (α lam : ℝ) :
    star (s2P α lam) = s2M α lam := by
  show (s2P α lam).adjoint = s2M α lam
  apply coord_ext
  intro f p
  rw [s2P, adjoint_coordOp, s2M, coordOp_coord,
    show (shiftFst (-1 : ℤ)).symm p = (p.1 + 1, p.2) from rfl]
  rw [star_mul, star_ofReal_complex, star_ph]
  simp only [shiftFst_apply]
  ring

theorem star_coord_s2M (α lam : ℝ) :
    star (s2M α lam) = s2P α lam := by
  show (s2M α lam).adjoint = s2P α lam
  apply coord_ext
  intro f p
  rw [s2M, adjoint_coordOp, s2P, coordOp_coord,
    show (shiftFst (1 : ℤ)).symm p = (p.1 - 1, p.2) from rfl]
  rw [star_mul, star_ofReal_complex, star_ph]
  rw [show ph α (- -((p.1 - 1, p.2).2)) = ph α ((p.1 - 1, p.2).2) from by congr 1; ring]
  simp only [shiftFst_apply]
  ring

theorem suspA_selfAdjoint_alt (α lam : ℝ) : IsSelfAdjoint (suspA α lam) := by
  change star (s2Sh + s2Sh' + s2P α lam + s2M α lam)
    = s2Sh + s2Sh' + s2P α lam + s2M α lam
  rw [StarRing.star_add, StarRing.star_add, StarRing.star_add, star_s2Sh, star_s2Sh', star_coord_s2P, star_coord_s2M]
  abel

def eps (p : ℤ × ℤ) : EllTwo2 := lp.single 2 p 1
def epsZ (k : ℤ) : EllTwo := lp.single 2 k 1

theorem coordOp_single {ι : Type*} [DecidableEq ι] (b : ι → ℂ) (e : ι ≃ ι) (K : ℝ)
    (hK0 : 0 ≤ K) (hK : ∀ i, ‖b i‖ ≤ K) (q : ι) :
    coordOp b e K hK0 hK (lp.single 2 q 1) = b (e.symm q) • lp.single 2 (e.symm q) 1 := by
  apply lp.ext
  funext i
  rw [coordOp_coord, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases h : e i = q
  · have hi : i = e.symm q := by rw [← h]; simp
    rw [if_pos h, if_pos hi, hi]
  · have hi : i ≠ e.symm q := fun hh => h (by rw [hh]; simp)
    rw [if_neg h, if_neg hi]
    ring

theorem s2Sh_eps (p : ℤ × ℤ) : s2Sh (eps p) = eps (p.1, p.2 - 1) := by
  rw [s2Sh, show eps p = lp.single 2 p 1 from rfl, coordOp_single, one_smul]
  rfl

theorem s2Sh'_eps (p : ℤ × ℤ) : s2Sh' (eps p) = eps (p.1, p.2 + 1) := by
  rw [s2Sh', show eps p = lp.single 2 p 1 from rfl, coordOp_single, one_smul]
  rfl

theorem s2P_eps (α lam : ℝ) (p : ℤ × ℤ) :
    s2P α lam (eps p) = ((lam : ℂ) * ph α p.2) • eps (p.1 + 1, p.2) := by
  rw [s2P, show eps p = lp.single 2 p 1 from rfl, coordOp_single]
  rfl

theorem s2M_eps (α lam : ℝ) (p : ℤ × ℤ) :
    s2M α lam (eps p) = ((lam : ℂ) * ph α (-p.2)) • eps (p.1 - 1, p.2) := by
  rw [s2M, show eps p = lp.single 2 p 1 from rfl, coordOp_single]
  rfl

theorem suspA_eps (α lam : ℝ) (p : ℤ × ℤ) :
    suspA α lam (eps p) = eps (p.1, p.2 - 1) + eps (p.1, p.2 + 1)
      + ((lam : ℂ) * ph α p.2) • eps (p.1 + 1, p.2)
      + ((lam : ℂ) * ph α (-p.2)) • eps (p.1 - 1, p.2) := by
  rw [suspA, add_apply, add_apply, add_apply, s2Sh_eps, s2Sh'_eps, s2P_eps, s2M_eps]

theorem shiftZ_epsZ (k l : ℤ) : shiftZ k (epsZ l) = epsZ (l - k) := by
  rw [shiftZ, show epsZ l = lp.single 2 l 1 from rfl, coordOp_single, one_smul]
  rfl

theorem amoPotOp_epsZ (α lam θ : ℝ) (l : ℤ) :
    amoPotOp α lam θ (epsZ l)
      = ((2 * lam * Real.cos (2 * Real.pi * (θ + (l : ℝ) * α)) : ℝ) : ℂ) • epsZ l := by
  rw [amoPotOp, diagZ, show epsZ l = lp.single 2 l 1 from rfl, coordOp_single]
  congr 1

theorem amoOp_epsZ (α lam ϑ : ℝ) (l : ℤ) :
    amoOp α lam ϑ (epsZ l) = epsZ (l - 1) + epsZ (l + 1)
      + ((2 * lam * Real.cos (2 * Real.pi * (ϑ + (l : ℝ) * α)) : ℝ) : ℂ) • epsZ l := by
  rw [amoOp, add_apply, add_apply, shiftZ_epsZ, shiftZ_epsZ, amoPotOp_epsZ]
  simp only [sub_neg_eq_add]

theorem fibVec_eps (ϑ : ℝ) (s : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∈ s) :
    fibVec ϑ (eps p : ℤ × ℤ → ℂ) s = phR ((p.1 : ℝ) * ϑ) • epsZ p.2 := by
  apply lp.ext
  funext n
  rw [fibVec_coord, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp only [eps, epsZ, lp.single_apply, Pi.single_apply]
  rw [Finset.sum_congr rfl (fun q _ => by rw [mul_ite, mul_one, mul_zero])]
  rw [Finset.sum_ite_eq']
  by_cases h : n = p.2
  · rw [if_pos (Finset.mem_filter.mpr ⟨hp, h.symm⟩), if_pos h, mul_one]
  · rw [if_neg (fun hc => h (Finset.mem_filter.mp hc).2.symm), if_neg h, mul_zero]

theorem fibVec_zero (ϑ : ℝ) (s : Finset (ℤ × ℤ)) : fibVec ϑ (0 : ℤ × ℤ → ℂ) s = 0 := by
  apply lp.ext
  funext n
  rw [fibVec_coord]
  simp

theorem fibVec_smul (ϑ : ℝ) (s : Finset (ℤ × ℤ)) (c : ℂ) (f : ℤ × ℤ → ℂ) :
    fibVec ϑ (c • f) s = c • fibVec ϑ f s := by
  rw [show (c • f) = (fun p => c * f p) from by funext p; simp]
  exact fibVec_const_mul ϑ c f s

theorem fibVec_sum (ϑ : ℝ) (s : Finset (ℤ × ℤ)) {ι : Type*} (t : Finset ι) (c : ι → ℂ)
    (f : ι → ℤ × ℤ → ℂ) :
    fibVec ϑ (∑ i ∈ t, c i • f i) s = ∑ i ∈ t, c i • fibVec ϑ (f i) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fibVec_zero]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [show (c a • f a) = (fun p => c a * f a p) from by funext p; simp]
      rw [fibVec_add, fibVec_const_mul, ih]

theorem two_cos_phase_mul (α lam ϑ : ℝ) (m k : ℤ) :
    phR ((m : ℝ) * ϑ) * ((2 * lam * Real.cos (2 * Real.pi * (ϑ + (k : ℝ) * α)) : ℝ) : ℂ)
      = ((lam : ℂ) * ph α k) * phR (((m + 1 : ℤ) : ℝ) * ϑ)
        + ((lam : ℂ) * ph α (-k)) * phR (((m - 1 : ℤ) : ℝ) * ϑ) := by
  rw [two_cos_phase]
  have h1 : phR ((m : ℝ) * ϑ) * phR ϑ = phR (((m + 1 : ℤ) : ℝ) * ϑ) := by
    rw [← phR_add]; congr 1; push_cast; ring
  have h2 : phR ((m : ℝ) * ϑ) * phR (-ϑ) = phR (((m - 1 : ℤ) : ℝ) * ϑ) := by
    rw [← phR_add]; congr 1; push_cast; ring
  rw [← h1, ← h2]
  ring

theorem fibVec_suspA_alt (α lam ϑ : ℝ) (v : EllTwo2) (s t : Finset (ℤ × ℤ))
    (hs : ∀ p : ℤ × ℤ, p ∉ s → (v : ℤ × ℤ → ℂ) p = 0)
    (ht : ∀ p : ℤ × ℤ, p ∉ t → (suspA α lam v : ℤ × ℤ → ℂ) p = 0) :
    amoOp α lam ϑ (fibVec ϑ (v : ℤ × ℤ → ℂ) s)
      = fibVec ϑ ((suspA α lam v : ℤ × ℤ → ℂ)) t := by
  classical
  set T : Finset (ℤ × ℤ) := t ∪ (s.image (fun p : ℤ × ℤ => (p.1, p.2 - 1))
      ∪ (s.image (fun p : ℤ × ℤ => (p.1, p.2 + 1))
      ∪ (s.image (fun p : ℤ × ℤ => (p.1 - 1, p.2))
      ∪ s.image (fun p : ℤ × ℤ => (p.1 + 1, p.2))))) with hT
  have hT1 : ∀ p ∈ s, (p.1, p.2 - 1) ∈ T := by
    intro p hp
    have him : (p.1, p.2 - 1) ∈ s.image (fun q : ℤ × ℤ => (q.1, q.2 - 1)) :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [hT]; simp only [Finset.mem_union]; tauto
  have hT2 : ∀ p ∈ s, (p.1, p.2 + 1) ∈ T := by
    intro p hp
    have him : (p.1, p.2 + 1) ∈ s.image (fun q : ℤ × ℤ => (q.1, q.2 + 1)) :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [hT]; simp only [Finset.mem_union]; tauto
  have hT3 : ∀ p ∈ s, (p.1 - 1, p.2) ∈ T := by
    intro p hp
    have him : (p.1 - 1, p.2) ∈ s.image (fun q : ℤ × ℤ => (q.1 - 1, q.2)) :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [hT]; simp only [Finset.mem_union]; tauto
  have hT4 : ∀ p ∈ s, (p.1 + 1, p.2) ∈ T := by
    intro p hp
    have him : (p.1 + 1, p.2) ∈ s.image (fun q : ℤ × ℤ => (q.1 + 1, q.2)) :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [hT]; simp only [Finset.mem_union]; tauto
  have hsuppT : ∀ q : ℤ × ℤ, (suspA α lam v : ℤ × ℤ → ℂ) q ≠ 0 → q ∈ T := by
    intro q hq
    obtain ⟨m, n⟩ := q
    rw [suspA_coord] at hq
    have h4 : (v : ℤ × ℤ → ℂ) (m, n + 1) ≠ 0 ∨ (v : ℤ × ℤ → ℂ) (m, n - 1) ≠ 0
        ∨ (v : ℤ × ℤ → ℂ) (m - 1, n) ≠ 0 ∨ (v : ℤ × ℤ → ℂ) (m + 1, n) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hq (by rw [hcon.1, hcon.2.1, hcon.2.2.1, hcon.2.2.2]; ring)
    rcases h4 with h | h | h | h
    · have hv : (m, n + 1) ∈ s := by by_contra hc; exact h (hs (m, n + 1) hc)
      simpa using hT1 (m, n + 1) hv
    · have hv : (m, n - 1) ∈ s := by by_contra hc; exact h (hs (m, n - 1) hc)
      simpa using hT2 (m, n - 1) hv
    · have hv : (m - 1, n) ∈ s := by by_contra hc; exact h (hs (m - 1, n) hc)
      simpa using hT4 (m - 1, n) hv
    · have hv : (m + 1, n) ∈ s := by by_contra hc; exact h (hs (m + 1, n) hc)
      simpa using hT3 (m + 1, n) hv
  have hTt : fibVec ϑ ((suspA α lam v : ℤ × ℤ → ℂ)) t
      = fibVec ϑ ((suspA α lam v : ℤ × ℤ → ℂ)) T :=
    fibVec_eq_of_support ϑ _ ht (fun p hp => by by_contra h; exact hp (hsuppT p h))
  have hvsum : v = ∑ p ∈ s, (v p) • eps p := by
    apply lp.ext
    funext q
    rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single q]
    · rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, show eps q = lp.single 2 q 1 from rfl,
        lp.single_apply, Pi.single_apply, if_pos rfl, mul_one]
    · intro b hb hbq
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, show eps b = lp.single 2 b 1 from rfl,
        lp.single_apply, Pi.single_apply, if_neg (fun h => hbq h.symm), mul_zero]
    · intro hq
      rw [hs q hq]
      simp
  have hbasis : ∀ p ∈ s, amoOp α lam ϑ (fibVec ϑ ((eps p : EllTwo2) : ℤ × ℤ → ℂ) s)
      = fibVec ϑ (((suspA α lam (eps p) : EllTwo2)) : ℤ × ℤ → ℂ) T := by
    intro p hp
    rw [fibVec_eps ϑ s p hp, map_smul, amoOp_epsZ, suspA_eps]
    simp only [lp.coeFn_add, lp.coeFn_smul]
    rw [fibVec_add, fibVec_add, fibVec_add, fibVec_smul, fibVec_smul,
      fibVec_eps ϑ T (p.1, p.2 - 1) (hT1 p hp), fibVec_eps ϑ T (p.1, p.2 + 1) (hT2 p hp),
      fibVec_eps ϑ T (p.1 + 1, p.2) (hT4 p hp), fibVec_eps ϑ T (p.1 - 1, p.2) (hT3 p hp)]
    simp only [smul_add, smul_smul, two_cos_phase_mul, add_smul]
    abel_nf
  conv_lhs => rw [hvsum]
  rw [show (((∑ p ∈ s, (v p) • eps p) : EllTwo2) : ℤ × ℤ → ℂ)
      = ∑ p ∈ s, (v p) • ((eps p : EllTwo2) : ℤ × ℤ → ℂ) from by
    rw [lp.coeFn_sum]
    exact Finset.sum_congr rfl (fun p _ => by rw [lp.coeFn_smul])]
  rw [fibVec_sum, map_sum]
  rw [hTt]
  conv_rhs => rw [hvsum]
  rw [show (((suspA α lam (∑ p ∈ s, (v p) • eps p)) : EllTwo2) : ℤ × ℤ → ℂ)
      = ∑ p ∈ s, (v p) • ((suspA α lam (eps p) : EllTwo2) : ℤ × ℤ → ℂ) from by
    rw [map_sum, lp.coeFn_sum]
    exact Finset.sum_congr rfl (fun p _ => by rw [map_smul, lp.coeFn_smul])]
  rw [fibVec_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [map_smul, hbasis p hp]

theorem phR_nat_pow (x : ℝ) (n : ℕ) : phR ((n : ℝ) * x) = (phR x) ^ n := by
  induction n with
  | zero => simp [phR_zero]
  | succ k ih =>
      rw [show (((k + 1 : ℕ) : ℝ) * x) = (k : ℝ) * x + x by push_cast; ring, phR_add, ih,
        pow_succ]

theorem phR_int_eq_one (r : ℤ) : phR (r : ℝ) = 1 := by
  rw [phR, show ((2 * Real.pi * (r : ℝ) : ℝ) : ℂ) * Complex.I
      = (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I r

theorem phR_eq_one_iff_int {x : ℝ} (hx : phR x = 1) : ∃ n : ℤ, x = n := by
  rw [phR, Complex.exp_eq_one_iff] at hx
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  have hIII : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I]; ring
  have h2 : ((2 * Real.pi * x : ℝ) : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    have h := congrArg (fun z : ℂ => z * (-Complex.I)) hn
    simpa only [mul_assoc, hIII, mul_one] using h
  have h3 : (2 * Real.pi * x : ℝ) = 2 * Real.pi * n := by
    rw [show ((n : ℂ) * (2 * (Real.pi : ℂ))) = ((((n : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) by
      push_cast; ring] at h2
    have h := Complex.ofReal_inj.mp h2
    rw [mul_comm ((n : ℝ)) (2 * Real.pi)] at h
    exact h
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h4 : x = (n : ℝ) := by
    apply mul_left_cancel₀ hπ
    linarith [h3]
  exact h4

theorem sum_phR_div (M : ℕ) (hM : 0 < M) (r : ℤ) :
    ∑ j ∈ Finset.range M, phR ((r : ℝ) * ((j : ℝ) / (M : ℝ)))
      = if (M : ℤ) ∣ r then (M : ℂ) else 0 := by
  set ζ : ℂ := phR ((r : ℝ) / (M : ℝ)) with hζ
  have hpow : ∀ j : ℕ, phR ((r : ℝ) * ((j : ℝ) / (M : ℝ))) = ζ ^ j := by
    intro j
    rw [hζ, ← phR_nat_pow]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun j _ => hpow j)]
  by_cases hdiv : (M : ℤ) ∣ r
  · have hζ1 : ζ = 1 := by
      obtain ⟨k, hk⟩ := hdiv
      have harg : (r : ℝ) / (M : ℝ) = (k : ℝ) := by
        rw [hk]
        push_cast
        rw [div_eq_iff (by positivity : (M : ℝ) ≠ 0)]
        ring
      rw [hζ, harg]
      exact phR_int_eq_one k
    rw [if_pos hdiv]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hζ1, one_pow])]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · rw [if_neg hdiv]
    have hζM : ζ ^ M = 1 := by
      rw [← hpow M]
      rw [show (r : ℝ) * ((M : ℝ) / (M : ℝ)) = (r : ℝ) by field_simp]
      exact phR_int_eq_one r
    have hζne : ζ ≠ 1 := by
      intro h1
      obtain ⟨k, hk⟩ := phR_eq_one_iff_int (by rw [← hζ]; exact h1)
      exact hdiv ⟨k, by
        have hMne : (M : ℝ) ≠ 0 := by positivity
        have : ((r : ℝ)) = (M : ℝ) * (k : ℝ) := by
          rw [← hk]; field_simp
        exact_mod_cast this⟩
    rw [geom_sum_eq hζne M, hζM, sub_self, zero_div]

theorem ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]

theorem sum_phR_conj_div (M : ℕ) (hM : 0 < M) (a b : ℤ) :
    ∑ j ∈ Finset.range M, phR ((a : ℝ) * ((j : ℝ) / (M : ℝ)))
        * conj (phR ((b : ℝ) * ((j : ℝ) / (M : ℝ))))
      = if (M : ℤ) ∣ (a - b) then (M : ℂ) else 0 := by
  have hcongr : ∀ j ∈ Finset.range M,
      phR ((a : ℝ) * ((j : ℝ) / (M : ℝ))) * conj (phR ((b : ℝ) * ((j : ℝ) / (M : ℝ))))
        = phR (((a - b : ℤ) : ℝ) * ((j : ℝ) / (M : ℝ))) := by
    intro j _
    rw [conj_phR, ← phR_add]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hcongr]
  exact sum_phR_div M hM (a - b)

theorem sum_fiber {N : Type*} [AddCommMonoid N] (s : Finset (ℤ × ℤ)) (T : Finset ℤ)
    (f : ℤ × ℤ → N) (hT : ∀ p ∈ s, p.2 ∈ T) :
    ∑ n ∈ T, ∑ p ∈ s.filter (fun p => p.2 = n), f p = ∑ p ∈ s, f p := by
  classical
  rw [Finset.sum_congr rfl (fun n _ =>
    Finset.sum_filter (fun p => p.2 = n) f)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.sum_ite_eq, if_pos (hT p hp)]

theorem sum_sq_orth {M : ℕ} (hM : 0 < M) (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ → ℂ)
    (hinj : ∀ p ∈ A, ∀ q ∈ A, w p ≠ 0 → w q ≠ 0 → (M : ℤ) ∣ (p.1 - q.1) → p = q) :
    ∑ j ∈ Finset.range M, ‖∑ p ∈ A, phR ((p.1 : ℝ) * ((j : ℝ) / (M : ℝ))) * w p‖ ^ 2
      = (M : ℝ) * ∑ p ∈ A, ‖w p‖ ^ 2 := by
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  have hexp : ∀ j : ℕ,
      ((‖∑ p ∈ A, phR ((p.1 : ℝ) * ((j : ℝ) / (M : ℝ))) * w p‖ ^ 2 : ℝ) : ℂ)
        = ∑ p ∈ A, ∑ q ∈ A,
            (phR ((p.1 : ℝ) * ((j : ℝ) / (M : ℝ))) * w p)
              * conj (phR ((q.1 : ℝ) * ((j : ℝ) / (M : ℝ))) * w q) := by
    intro j
    rw [ofReal_norm_sq, map_sum (starRingEnd ℂ)
      (fun p => phR ((p.1 : ℝ) * ((j : ℝ) / (M : ℝ))) * w p) A, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun j _ => hexp j)]
  have h1 : (∑ j ∈ Finset.range M, ∑ p ∈ A, ∑ q ∈ A,
        (phR ((p.1 : ℝ) * ((j : ℝ) / (M : ℝ))) * w p)
          * conj (phR ((q.1 : ℝ) * ((j : ℝ) / (M : ℝ))) * w q))
      = ∑ p ∈ A, ∑ q ∈ A, (w p * conj (w q))
          * (∑ j ∈ Finset.range M, phR ((p.1 : ℝ) * ((j : ℝ) / (M : ℝ)))
              * conj (phR ((q.1 : ℝ) * ((j : ℝ) / (M : ℝ))))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul]
    ring
  rw [h1]
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => by
    rw [sum_phR_conj_div M hM p.1 q.1]))]
  have h3 : ∀ p ∈ A, (∑ q ∈ A,
        (w p * conj (w q)) * (if (M : ℤ) ∣ (p.1 - q.1) then (M : ℂ) else 0))
      = w p * conj (w p) * (M : ℂ) := by
    intro p hp
    have h1' : (∑ q ∈ A,
        (w p * conj (w q)) * (if (M : ℤ) ∣ (p.1 - q.1) then (M : ℂ) else 0))
        = (w p * conj (w p)) * (if (M : ℤ) ∣ (p.1 - p.1) then (M : ℂ) else 0) :=
      Finset.sum_eq_single p (fun q hq hqp => by
        by_cases hwp : w p = 0
        · simp [hwp]
        · by_cases hwq : w q = 0
          · simp [hwq]
          · rw [if_neg (fun hd => hqp (hinj p hp q hq hwp hwq hd).symm)]
            ring)
        (fun hp' => absurd hp hp')
    rw [sub_self, if_pos (dvd_zero (M : ℤ))] at h1'
    rw [h1']
  rw [Finset.sum_congr rfl h3]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [ofReal_norm_sq]
  push_cast
  ring

theorem fibVec_parseval_zero {M : ℕ} (hM : 0 < M) (w : ℤ × ℤ → ℂ) (s : Finset (ℤ × ℤ))
    (hs : ∀ p : ℤ × ℤ, p ∉ s → w p = 0)
    (hinj : ∀ p q : ℤ × ℤ, w p ≠ 0 → w q ≠ 0 → p.2 = q.2 → (M : ℤ) ∣ (p.1 - q.1) → p = q) :
    ∑ j ∈ Finset.range M, ‖fibVec ((j : ℝ) / (M : ℝ)) w s‖ ^ 2
      = (M : ℝ) * ∑ p ∈ s, ‖w p‖ ^ 2 := by
  classical
  set T : Finset ℤ := s.image (fun p : ℤ × ℤ => p.2) with hT
  have hfibsupp : ∀ (j : ℕ) (n : ℤ), n ∉ T → fibVec ((j : ℝ) / (M : ℝ)) w s n = 0 := by
    intro j n hn
    rw [fibVec_coord]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    exact absurd (Finset.mem_image.mpr ⟨p, hp.1, hp.2⟩) hn
  have hstep1 : ∀ j : ℕ, ‖fibVec ((j : ℝ) / (M : ℝ)) w s‖ ^ 2
      = ∑ n ∈ T, ‖fibVec ((j : ℝ) / (M : ℝ)) w s n‖ ^ 2 :=
    fun j => lp_norm_sq_eq_sum _ T (fun n hn => hfibsupp j n hn)
  rw [Finset.sum_congr rfl (fun j _ => hstep1 j)]
  rw [Finset.sum_comm]
  have hinner : ∀ n ∈ T, ∑ j ∈ Finset.range M, ‖fibVec ((j : ℝ) / (M : ℝ)) w s n‖ ^ 2
      = (M : ℝ) * ∑ p ∈ s.filter (fun p => p.2 = n), ‖w p‖ ^ 2 := by
    intro n _
    rw [Finset.sum_congr rfl (fun j _ => by rw [fibVec_coord])]
    exact sum_sq_orth hM _ w (fun p hp q hq hp' hq' hd => hinj p q hp' hq'
      (by rw [(Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hq).2]) hd)
  rw [Finset.sum_congr rfl hinner]
  rw [← Finset.mul_sum]
  congr 1
  exact sum_fiber s T (fun p => ‖w p‖ ^ 2) (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem algebraMap_apply_smul {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (c : ℂ) (x : X) : (algebraMap ℂ (X →L[ℂ] X) c) x = c • x := by
  rw [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self]

theorem fibVec_amoOp_sub_alt (α lam ϑ z : ℝ) (v : EllTwo2) (s t : Finset (ℤ × ℤ))
    (hs : ∀ p : ℤ × ℤ, p ∉ s → (v : ℤ × ℤ → ℂ) p = 0)
    (hvt : ∀ p : ℤ × ℤ, p ∉ t → (v : ℤ × ℤ → ℂ) p = 0)
    (hst : ∀ p : ℤ × ℤ, p ∉ t → (suspA α lam v : ℤ × ℤ → ℂ) p = 0) :
    (amoOp α lam ϑ - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) z) (fibVec ϑ (v : ℤ × ℤ → ℂ) s)
      = fibVec ϑ (((suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v :
          EllTwo2) : ℤ × ℤ → ℂ) t := by
  rw [sub_apply, algebraMap_apply_smul, fibVec_suspA_alt α lam ϑ v s t hs hst]
  rw [← fibVec_const_mul ϑ ((z : ℝ) : ℂ) (v : ℤ × ℤ → ℂ) s]
  have hcongr : fibVec ϑ (fun p : ℤ × ℤ => ((z : ℝ) : ℂ) * (v : ℤ × ℤ → ℂ) p) s
      = fibVec ϑ (fun p : ℤ × ℤ => ((z : ℝ) : ℂ) * (v : ℤ × ℤ → ℂ) p) t :=
    fibVec_eq_of_support ϑ _ (fun p hp => by rw [hs p hp, mul_zero])
      (fun p hp => by rw [hvt p hp, mul_zero])
  rw [hcongr, ← fibVec_sub]
  suffices h : ((suspA α lam) v : ℤ × ℤ → ℂ) -
        (fun p : ℤ × ℤ => ((z : ℝ) : ℂ) * (v : ℤ × ℤ → ℂ) p)
      = (((suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v : EllTwo2) :
          ℤ × ℤ → ℂ) by
    rw [h]
  funext p
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, algebraMap_apply_smul, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]

end TMAux

open TMAux

theorem spectrum_suspA_subset_amoOp (α lam : ℝ) (hα : Irrational α) :
    spectrum ℂ (Work.TMComp.Duality.suspA α lam) ⊆ spectrum ℂ (Work.TMComp.Duality.amoOp α lam 0) := by
  classical
  intro E hE
  have hsa : IsSelfAdjoint (suspA α lam) := suspA_selfAdjoint_alt α lam
  have hEre : E = ((E.re : ℝ) : ℂ) := hsa.mem_spectrum_eq_re hE
  set z : ℝ := E.re with hzdef
  by_contra hcon
  have hznot : (z : ℂ) ∉ spectrum ℂ (amoOp α lam 0) := fun hz => hcon (by rw [hEre]; exact hz)
  obtain ⟨d, hd0, hd⟩ := spectrum_gap_of_notMem (amoOp α lam 0) z hznot
  have hfiber : ∀ (ϑ : ℝ) (x : EllTwo), d * ‖x‖
      ≤ ‖(amoOp α lam ϑ - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) z) x‖ := by
    intro ϑ x
    refine norm_le_of_spectrum_avoid (amoOp α lam ϑ) (amoOp_selfAdjoint α lam ϑ) z hd0 ?_ x
    intro w hw
    rw [amoOp_spectrum_phase α lam hα ϑ 0] at hw
    exact hd w hw
  -- the bound for finitely supported vectors
  have hfin : ∀ v : EllTwo2, (∃ s : Finset (ℤ × ℤ), ∀ p ∉ s, (v : ℤ × ℤ → ℂ) p = 0) →
      d * ‖v‖ ≤ ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v‖ := by
    intro v ⟨s₀, hs₀⟩
    set t₀ : Finset (ℤ × ℤ) := s₀ ∪ (s₀.image (fun p : ℤ × ℤ => (p.1, p.2 - 1))
        ∪ (s₀.image (fun p : ℤ × ℤ => (p.1, p.2 + 1))
        ∪ (s₀.image (fun p : ℤ × ℤ => (p.1 - 1, p.2))
        ∪ s₀.image (fun p : ℤ × ℤ => (p.1 + 1, p.2))))) with ht₀
    have hs₀t₀ : ∀ p ∈ s₀, p ∈ t₀ := by
      intro p hp; rw [ht₀]; simp only [Finset.mem_union]; tauto
    obtain ⟨a, b, W, hW0, hW2, hbox⟩ := exists_box2 t₀
    have hbox' : ∀ p ∈ t₀, p.1 ∈ Set.Icc a (a + (W : ℤ) - 1) ∧
        p.2 ∈ Set.Icc b (b + (W : ℤ) - 1) := hbox
    set s : Finset (ℤ × ℤ) :=
      Finset.Icc a (a + (W : ℤ) - 1) ×ˢ Finset.Icc b (b + (W : ℤ) - 1) with hsdef
    set t : Finset (ℤ × ℤ) :=
      Finset.Icc (a - 1) (a + (W : ℤ)) ×ˢ Finset.Icc (b - 1) (b + (W : ℤ)) with htdef
    have hvs : ∀ p : ℤ × ℤ, p ∉ s → (v : ℤ × ℤ → ℂ) p = 0 := by
      intro p hp
      by_contra hne
      have hpt₀ : p ∈ t₀ := by
        by_contra hc
        exact hne (hs₀ p (fun hps => hc (hs₀t₀ p hps)))
      have hb := hbox' p hpt₀
      exact hp (by
        rw [hsdef, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        exact ⟨⟨hb.1.1, hb.1.2⟩, ⟨hb.2.1, hb.2.2⟩⟩)
    have hvt : ∀ p : ℤ × ℤ, p ∉ t → (v : ℤ × ℤ → ℂ) p = 0 := by
      intro p hp
      apply hvs p
      intro hps
      refine hp ?_
      rw [hsdef, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hps
      rw [htdef, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    have hst : ∀ p : ℤ × ℤ, p ∉ t → (suspA α lam v : ℤ × ℤ → ℂ) p = 0 := by
      intro p hp
      by_contra hne
      obtain ⟨m, n⟩ := p
      rw [suspA_coord] at hne
      have h4 : (v : ℤ × ℤ → ℂ) (m, n + 1) ≠ 0 ∨ (v : ℤ × ℤ → ℂ) (m, n - 1) ≠ 0
          ∨ (v : ℤ × ℤ → ℂ) (m - 1, n) ≠ 0 ∨ (v : ℤ × ℤ → ℂ) (m + 1, n) ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hne (by rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]; ring)
      refine hp ?_
      rw [htdef, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      rcases h4 with h | h | h | h
      · have hq : (m, n + 1) ∈ s₀ := by by_contra hc; exact h (hs₀ _ hc)
        have hb := hbox' (m, n + 1) (hs₀t₀ _ hq)
        have hb1 : a ≤ m := hb.1.1
        have hb2 : m ≤ a + (W : ℤ) - 1 := hb.1.2
        have hb3 : b ≤ n + 1 := hb.2.1
        have hb4 : n + 1 ≤ b + (W : ℤ) - 1 := hb.2.2
        exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
      · have hq : (m, n - 1) ∈ s₀ := by by_contra hc; exact h (hs₀ _ hc)
        have hb := hbox' (m, n - 1) (hs₀t₀ _ hq)
        have hb1 : a ≤ m := hb.1.1
        have hb2 : m ≤ a + (W : ℤ) - 1 := hb.1.2
        have hb3 : b ≤ n - 1 := hb.2.1
        have hb4 : n - 1 ≤ b + (W : ℤ) - 1 := hb.2.2
        exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
      · have hq : (m - 1, n) ∈ s₀ := by by_contra hc; exact h (hs₀ _ hc)
        have hb := hbox' (m - 1, n) (hs₀t₀ _ hq)
        have hb1 : a ≤ m - 1 := hb.1.1
        have hb2 : m - 1 ≤ a + (W : ℤ) - 1 := hb.1.2
        have hb3 : b ≤ n := hb.2.1
        have hb4 : n ≤ b + (W : ℤ) - 1 := hb.2.2
        exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
      · have hq : (m + 1, n) ∈ s₀ := by by_contra hc; exact h (hs₀ _ hc)
        have hb := hbox' (m + 1, n) (hs₀t₀ _ hq)
        have hb1 : a ≤ m + 1 := hb.1.1
        have hb2 : m + 1 ≤ a + (W : ℤ) - 1 := hb.1.2
        have hb3 : b ≤ n := hb.2.1
        have hb4 : n ≤ b + (W : ℤ) - 1 := hb.2.2
        exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    have hNpos : (0 : ℕ) < W + 3 := by omega
    have hinjv : ∀ p q : ℤ × ℤ, (v : ℤ × ℤ → ℂ) p ≠ 0 → (v : ℤ × ℤ → ℂ) q ≠ 0 →
        p.2 = q.2 → ((W + 3 : ℕ) : ℤ) ∣ (p.1 - q.1) → p = q := by
      intro p q hp hq hpq hdvd
      have hps : p ∈ s := by by_contra hc; exact hp (hvs p hc)
      have hqs : q ∈ s := by by_contra hc; exact hq (hvs q hc)
      rw [hsdef, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hps hqs
      have habs : |p.1 - q.1| ≤ (W : ℤ) - 1 := by
        rw [abs_sub_le_iff]; constructor <;> omega
      have hlt : |p.1 - q.1| < ((W + 3 : ℕ) : ℤ) := by
        have : ((W + 3 : ℕ) : ℤ) = (W : ℤ) + 3 := by push_cast; ring
        omega
      have hsub : p.1 - q.1 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      exact Prod.ext (sub_eq_zero.mp hsub) hpq
    set R : EllTwo2 := (suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v with hRdef
    have hRt : ∀ p : ℤ × ℤ, p ∉ t → (R : ℤ × ℤ → ℂ) p = 0 := by
      intro p hp
      have h1 := hst p hp
      have h2 := hvt p hp
      rw [hRdef, sub_apply, lp.coeFn_sub, Pi.sub_apply, algebraMap_apply_smul,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, h1, h2]
      ring
    have hinjR : ∀ p q : ℤ × ℤ, (R : ℤ × ℤ → ℂ) p ≠ 0 → (R : ℤ × ℤ → ℂ) q ≠ 0 →
        p.2 = q.2 → ((W + 3 : ℕ) : ℤ) ∣ (p.1 - q.1) → p = q := by
      intro p q hp hq hpq hdvd
      have hpt : p ∈ t := by by_contra hc; exact hp (hRt p hc)
      have hqt : q ∈ t := by by_contra hc; exact hq (hRt q hc)
      rw [htdef, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hpt hqt
      have habs : |p.1 - q.1| ≤ (W : ℤ) + 1 := by
        rw [abs_sub_le_iff]; constructor <;> omega
      have hlt : |p.1 - q.1| < ((W + 3 : ℕ) : ℤ) := by
        have : ((W + 3 : ℕ) : ℤ) = (W : ℤ) + 3 := by push_cast; ring
        omega
      have hsub : p.1 - q.1 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      exact Prod.ext (sub_eq_zero.mp hsub) hpq
    have hpv := fibVec_parseval_zero hNpos (v : ℤ × ℤ → ℂ) s hvs hinjv
    have hpR := fibVec_parseval_zero hNpos (R : ℤ × ℤ → ℂ) t hRt hinjR
    have hnormv : ∑ p ∈ s, ‖(v : ℤ × ℤ → ℂ) p‖ ^ 2 = ‖v‖ ^ 2 :=
      (lp_norm_sq_eq_sum v s hvs).symm
    have hnormR : ∑ p ∈ t, ‖(R : ℤ × ℤ → ℂ) p‖ ^ 2 = ‖R‖ ^ 2 :=
      (lp_norm_sq_eq_sum R t hRt).symm
    have hper : ∀ j ∈ Finset.range (W + 3),
        d ^ 2 * ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (v : ℤ × ℤ → ℂ) s‖ ^ 2
          ≤ ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (R : ℤ × ℤ → ℂ) t‖ ^ 2 := by
      intro j _
      have hx := hfiber ((j : ℝ) / ((W + 3 : ℕ) : ℝ))
        (fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (v : ℤ × ℤ → ℂ) s)
      have hb := fibVec_amoOp_sub_alt α lam ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) z v s t hvs hvt hst
      rw [hb] at hx
      have hx2 : (d * ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (v : ℤ × ℤ → ℂ) s‖) ^ 2
          ≤ ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (R : ℤ × ℤ → ℂ) t‖ ^ 2 := by
        have h2 : 0 ≤ d * ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (v : ℤ × ℤ → ℂ) s‖ :=
          mul_nonneg hd0.le (norm_nonneg _)
        calc (d * ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (v : ℤ × ℤ → ℂ) s‖) ^ 2
            = (d * ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (v : ℤ × ℤ → ℂ) s‖)
              * (d * ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (v : ℤ × ℤ → ℂ) s‖) := by ring
          _ ≤ ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (R : ℤ × ℤ → ℂ) t‖
              * ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (R : ℤ × ℤ → ℂ) t‖ :=
              mul_le_mul hx hx h2 (le_trans h2 hx)
          _ = ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (R : ℤ × ℤ → ℂ) t‖ ^ 2 := by ring
      rw [mul_pow] at hx2
      exact hx2
    have hsum := Finset.sum_le_sum hper
    rw [hnormv] at hpv
    rw [hnormR] at hpR
    have hLHS : ∑ j ∈ Finset.range (W + 3),
        d ^ 2 * ‖fibVec ((j : ℝ) / ((W + 3 : ℕ) : ℝ)) (v : ℤ × ℤ → ℂ) s‖ ^ 2
        = d ^ 2 * (((W + 3 : ℕ) : ℝ) * ‖v‖ ^ 2) := by
      rw [← Finset.mul_sum, hpv]
    rw [hLHS, hpR] at hsum
    have hNposR : (0 : ℝ) < ((W + 3 : ℕ) : ℝ) := by positivity
    have h1 : (d ^ 2 * ‖v‖ ^ 2) * ((W + 3 : ℕ) : ℝ) ≤ ‖R‖ ^ 2 * ((W + 3 : ℕ) : ℝ) := by
      linarith [hsum]
    have h2 : d ^ 2 * ‖v‖ ^ 2 ≤ ‖R‖ ^ 2 := le_of_mul_le_mul_right h1 hNposR
    have h3 : (d * ‖v‖) ^ 2 ≤ ‖R‖ ^ 2 := by rw [mul_pow]; exact h2
    have h4 : |d * ‖v‖| ≤ |‖R‖| := sq_le_sq.mp h3
    rwa [abs_of_nonneg (mul_nonneg hd0.le (norm_nonneg _)), abs_of_nonneg (norm_nonneg _)] at h4
  -- extend to all vectors by density
  have hall : ∀ v : EllTwo2, d * ‖v‖
      ≤ ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v‖ := by
    intro v
    set C : ℝ := ‖suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z‖ with hCdef
    have hCnn : 0 ≤ C := norm_nonneg _
    have hden : 0 < C + d + 1 := by linarith
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨s, hs⟩ := exists_finsupp_close_lp v (div_pos hε hden)
    set v' : EllTwo2 := ∑ i ∈ s, lp.single 2 i (v i) with hv'
    have hv'supp : ∃ s' : Finset (ℤ × ℤ), ∀ p ∉ s', (v' : ℤ × ℤ → ℂ) p = 0 := by
      refine ⟨s, ?_⟩
      intro p hp
      rw [hv', lp.coeFn_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      rw [lp.single_apply, Pi.single_eq_of_ne]
      intro h; exact hp (h ▸ hi)
    have hfin' := hfin v' hv'supp
    have hclose : ‖v' - v‖ < ε / (C + d + 1) := by rw [hv']; exact hs
    have hclose' : ‖v - v'‖ < ε / (C + d + 1) := by rwa [norm_sub_rev] at hclose
    have hdecomp : (suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v
        = (suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v'
          + (suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) (v - v') := by
      rw [← map_add]; congr 1; abel
    have hCv : ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) (v - v')‖
        ≤ C * ‖v - v'‖ := by rw [hCdef]; exact ContinuousLinearMap.le_opNorm _ _
    have hnormv' : ‖v‖ - ε / (C + d + 1) ≤ ‖v'‖ := by
      have h1 : |‖v'‖ - ‖v‖| ≤ ‖v' - v‖ := abs_norm_sub_norm_le v' v
      rw [abs_le] at h1
      linarith [h1.1, hclose]
    have hAv : ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v'‖
        ≤ ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v‖ + C * ‖v - v'‖ := by
      have hdec2 : (suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v'
          = (suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v
            - (suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) (v - v') := by
        rw [← map_sub]; congr 1; abel
      rw [hdec2]
      have h1 : ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v
          - (suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) (v - v')‖
          ≤ ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v‖
            + ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) (v - v')‖ :=
        norm_sub_le _ _
      linarith [h1, hCv]
    have hfrac : (C + d) * (ε / (C + d + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hden]
      nlinarith [hε, hd0, hCnn]
    have hstep1 : d * ‖v‖ - d * (ε / (C + d + 1)) ≤ d * ‖v'‖ := by
      have h := mul_le_mul_of_nonneg_left hnormv' hd0.le
      rw [mul_sub] at h
      exact h
    have hA2 : ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v'‖
        ≤ ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v‖
          + C * (ε / (C + d + 1)) := by
      have hCmul : C * ‖v - v'‖ ≤ C * (ε / (C + d + 1)) :=
        mul_le_mul_of_nonneg_left hclose'.le hCnn
      linarith [hAv, hCmul]
    have hstep2 : d * ‖v‖ - d * (ε / (C + d + 1))
        ≤ ‖(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) v‖
          + C * (ε / (C + d + 1)) := by
      linarith [hstep1, hfin', hA2]
    have hstep3 : d * (ε / (C + d + 1)) + C * (ε / (C + d + 1)) ≤ ε := by
      nlinarith [hfrac]
    linarith [hstep2, hstep3]
  -- conclusion
  have hunit : IsUnit (suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) :=
    isUnit_of_lower_bound _ (hsa.sub (IsSelfAdjoint.algebraMap _ (by
      rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]))) hd0 hall
  have hnot : (z : ℂ) ∉ spectrum ℂ (suspA α lam) := by
    rw [spectrum.notMem_iff]
    have h : algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z - (suspA α lam)
        = -(suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) z) := by abel
    rw [h]
    exact hunit.neg
  exact hnot (hEre ▸ hE)

end Work.TMComp.Duality

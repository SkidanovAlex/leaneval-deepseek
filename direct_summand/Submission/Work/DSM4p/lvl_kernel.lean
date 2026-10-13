import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.lvlP_charP
import Submission.Work.DSM4p.lvl_torsionFree
import Submission.Work.DSM4p.lvl_teich_mem_span_p
import Submission.Work.DSM4p.exists_untilt_lift
import Submission.Work.DSM4p.kerP

/-!
# DSM4p — the kernel clause `lvl_kernel` of Route U

This is step **(3)** of the Route U plan (`Submission/Work/DSM4p/Plan.lean`): if `x : B` has image
in the untilted level `lvl Q hgr N` lying in `(p^m)`, and `m * p^(k+m+3) ≤ N`, then
`Q.ϖ k * gr k * x ∈ (p^m : B)`.

Write `B♭ := PreTilt B p`, `g♭ := tiltTower gr hgr`, `ϖ♭ := varpiTower Q = tiltTower Q.ϖ Q.root`
(so `ϖ♭ 0 = DSM5c.tiltVarpi Q`), `R_N := lvlP Q hgr N = chartRing g♭ ϖ♭ N` and
`φ := algebraMap B♭ R_N`.  The proof has three ingredients, following the plan:

* **`lvl_kernel_step`** — the `m = 1` case.  From `algebraMap x ∈ (p : lvl N)` we lift `x`
  modulo `p` to the tilt (`exists_untilt_lift`), transport the resulting Teichmüller class
  backwards along `teich_algebraMap` (via `lvl_algebraMap_eq`) to obtain
  `φ x♭ ∈ (φ ϖ♭ 0)^p ⊆ R_N` (`lvl_teich_mem_span_p`), apply the characteristic-`p` Hartogs
  estimate `kerP` to the tilted root systems, and descend along `♯ = PreTilt.untilt` using
  `Q.unit` (`Q.ϖ 0 ^ p = p · v` with `v` a unit).  The `p` in the exponent `(T 0)^p` of `kerP` is
  exactly what converts `ϖ♭ 0 ^ p = p · v` into divisibility by `p` in `B`.
* **`lvl_kernel_devissage_aux`** — the dévissage from `m = 1` to `m`, iterating the `m = 1` step
  for the element `a := Q.ϖ (k+m) gr (k+m)`, whose `p^m`-th power is `Q.ϖ k gr k`;
  `lvl_torsionFree` is what makes each iteration decrease the exponent `p^m` by one power.
* the assembly, which multiplies by the complementary power `a^(p^m - m)`.
-/

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

section Core

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
variable [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]

/-- **The tilt of the `ϖ`-tower** of `Q` — the system `ϖ♭ := tiltTower Q.ϖ Q.root` of the plan,
written through a wrapper so that the root-system proof of `Q` (which is a `PerfectoidData` field
rather than a hypothesis, hence only definitionally an `IsRootSystem`) does not have to be
re-elaborated inside tactic goals. -/
noncomputable def varpiTower (Q : PerfectoidData p B) : ℕ → PreTilt B p :=
  tiltTower Q.ϖ Q.root

theorem varpiTower_isRootSystem (Q : PerfectoidData p B) : IsRootSystem p (varpiTower Q) :=
  tiltTower_isRootSystem Q.ϖ Q.root

theorem varpiTower_zero (Q : PerfectoidData p B) : varpiTower Q 0 = DSM5c.tiltVarpi Q :=
  tiltTower_zero Q.ϖ Q.root

theorem untilt_varpiTower (Q : PerfectoidData p B) (k : ℕ) :
    PreTilt.untilt (varpiTower Q k) = Q.ϖ k :=
  untilt_tiltTower Q.ϖ Q.root k

/-- The `B`-algebra structure of the untilted level `lvl Q hgr N` is `untiltOf.algebraMap` of the
characteristic-`p` level: this is `lvlAlg`, read as an equality of ring homomorphisms. -/
theorem lvl_algebraMap_eq (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) :
    (algebraMap B (lvl Q hgr N)) =
      (DSM5c.untiltOf.algebraMap (p := p) (W := B) (surjective_fontaineTheta Q)
        (algebraMap (PreTilt B p) (lvlP Q hgr N))) :=
  RingHom.algebraMap_toAlgebra _

/-- **The `m = 1` case of the kernel clause.**  If the image of `y : B` in the untilted level
`lvl Q hgr N` is divisible by `p`, and `p^(L+3) ≤ N` (the level shift `p·p^(L+2)` required by the
Hartogs estimate `kerP`), then `Q.ϖ (L+1) * gr (L+1) * y` is divisible by `p` in `B`. -/
theorem lvl_kernel_step (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (hgr0 : gr 0 ≠ 0) (L N : ℕ) (hLN : p ^ (L + 3) ≤ N) {y : B}
    (hy : algebraMap B (lvl Q hgr N) y ∈ Ideal.span {(p : lvl Q hgr N)}) :
    ∃ c : B, Q.ϖ (L + 1) * gr (L + 1) * y = (p : B) * c := by
  have hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := B)) :=
    surjective_fontaineTheta Q
  -- (a) lift `y` modulo `p` to the tilt
  obtain ⟨xb, hxb⟩ := exists_untilt_lift Q y
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hxb
  have he' : PreTilt.untilt xb = y + (p : B) * e := by
    rw [show PreTilt.untilt xb = (PreTilt.untilt xb - y) + y from by ring, ← he]
    ring
  -- (b) the Teichmüller class of `φ xb` is divisible by `p` in the level
  have hmk : (DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (lvlP Q hgr N)))
        (WittVector.teichmuller p (algebraMap (PreTilt B p) (lvlP Q hgr N) xb)) ∈
      Ideal.span {(p : lvl Q hgr N)} := by
    rw [DSM5c.Eta.U.teich_algebraMap (p := p) (W := B) hθ
        (algebraMap (PreTilt B p) (lvlP Q hgr N)) xb,
      ← lvl_algebraMap_eq Q hgr N, he']
    rw [map_add, map_mul, map_natCast]
    exact Ideal.add_mem _ hy (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  -- (c) the characteristic-`p` membership in `lvlP`
  have hR : algebraMap (PreTilt B p) (lvlP Q hgr N) xb ∈
      Ideal.span {((algebraMap (PreTilt B p) (lvlP Q hgr N) (DSM5c.tiltVarpi Q))) ^ p} :=
    (lvl_teich_mem_span_p Q hgr hgr0 N (algebraMap (PreTilt B p) (lvlP Q hgr N) xb)).mp hmk
  -- (d) the Hartogs estimate over the tilt
  have hT0 : IsSMulRegular (PreTilt B p) (varpiTower Q 0) := by
    rw [varpiTower_zero, IsSMulRegular]
    intro u v huv
    have huveq : DSM5c.tiltVarpi Q * u = DSM5c.tiltVarpi Q * v := by
      simpa [smul_eq_mul] using huv
    have h : DSM5c.tiltVarpi Q * (u - v) = 0 := by
      rw [mul_sub, huveq, sub_self]
    exact sub_eq_zero.mp (DSM5c.Regularity.tiltVarpi_isSMulRegular Q (u - v) h)
  have hker := kerP (p := p) (R := PreTilt B p) (G := tiltTower gr hgr)
    (T := varpiTower Q) (tiltTower_isRootSystem gr hgr) (varpiTower_isRootSystem Q) hT0 L p N
    (by rw [mul_comm, ← pow_succ]; exact hLN) xb
    (by rw [varpiTower_zero]; exact hR)
  -- (e) descend along `♯`
  obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.mp hker
  obtain ⟨v, hv⟩ := Q.unit
  have htilt : Q.ϖ (L + 1) * gr (L + 1) * PreTilt.untilt xb =
      (p : B) * ((v : B) * PreTilt.untilt δ) := by
    have h := congrArg PreTilt.untilt hδ
    simp only [map_mul, map_pow] at h
    rw [untilt_varpiTower Q (L + 1), untilt_tiltTower gr hgr (L + 1),
      untilt_varpiTower Q 0] at h
    rw [← h, hv]
    ring
  refine ⟨(v : B) * PreTilt.untilt δ - Q.ϖ (L + 1) * gr (L + 1) * e, ?_⟩
  have hy' : y = PreTilt.untilt xb - (p : B) * e := by rw [he']; ring
  rw [hy', mul_sub, htilt]
  ring

/-- **The dévissage of the kernel clause.**  Assume the `m = 1` statement for a fixed element
`a : B`: every `b : B` whose image in `lvl Q hgr N` is divisible by `p` satisfies `a * b ∈ pB`.
Then from `algebraMap x ∈ (p^m : lvl Q hgr N)` we get `a^m * x ∈ (p^m : B)`.

The induction step uses `lvl_torsionFree` to cancel the extra power of `p`: if `a x = p b` and
`algebraMap x ∈ (p^(m+1))`, then `p · algebraMap b = algebraMap a · algebraMap x` is divisible by
`p^(m+1)`, hence `algebraMap b ∈ (p^m)` and the induction hypothesis applies to `b`. -/
theorem lvl_kernel_devissage_aux (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) {a : B}
    (H : ∀ b : B, algebraMap B (lvl Q hgr N) b ∈ Ideal.span {(p : lvl Q hgr N)} →
      ∃ c : B, a * b = (p : B) * c)
    (m : ℕ) (x : B) (hx : algebraMap B (lvl Q hgr N) x ∈
      Ideal.span {((p : lvl Q hgr N)) ^ m}) :
    ∃ c : B, a ^ m * x = (p : B) ^ m * c := by
  induction m generalizing x with
  | zero => exact ⟨x, by simp⟩
  | succ m ih =>
    -- the image of `x` is divisible by `p`
    have hpx : algebraMap B (lvl Q hgr N) x ∈ Ideal.span {(p : lvl Q hgr N)} :=
      (Ideal.span_singleton_le_span_singleton.mpr
        ⟨(p : lvl Q hgr N) ^ m, pow_succ' _ m⟩) hx
    obtain ⟨b, hb⟩ := H x hpx
    -- the image of `b` is divisible by `p^m`
    have hbm : algebraMap B (lvl Q hgr N) b ∈ Ideal.span {((p : lvl Q hgr N)) ^ m} := by
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hx
      have hreg := lvl_torsionFree Q hgr N
      have h1 : algebraMap B (lvl Q hgr N) (a * x) =
          (p : lvl Q hgr N) * algebraMap B (lvl Q hgr N) b := by
        calc algebraMap B (lvl Q hgr N) (a * x)
            = algebraMap B (lvl Q hgr N) ((p : B) * b) := by rw [hb]
          _ = (p : lvl Q hgr N) * algebraMap B (lvl Q hgr N) b := by
              rw [map_mul, map_natCast]
      have key : (p : lvl Q hgr N) * algebraMap B (lvl Q hgr N) b =
          (p : lvl Q hgr N) *
            ((p : lvl Q hgr N) ^ m * (algebraMap B (lvl Q hgr N) a * w)) := by
        rw [← h1, map_mul, ← hw, pow_succ]
        ring
      have hb' : algebraMap B (lvl Q hgr N) b =
          (p : lvl Q hgr N) ^ m * (algebraMap B (lvl Q hgr N) a * w) :=
        hreg (by simpa [smul_eq_mul] using key)
      exact Ideal.mem_span_singleton'.mpr ⟨algebraMap B (lvl Q hgr N) a * w,
        by rw [hb']; ring⟩
    obtain ⟨c, hc⟩ := ih b hbm
    exact ⟨c, by
      calc a ^ (m + 1) * x
          = a ^ m * (a * x) := by rw [pow_succ]; ring
        _ = a ^ m * ((p : B) * b) := by rw [hb]
        _ = (p : B) * (a ^ m * b) := by ring
        _ = (p : B) * ((p : B) ^ m * c) := by rw [hc]
        _ = (p : B) ^ (m + 1) * c := by rw [pow_succ]; ring⟩

end Core

theorem lvl_kernel {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr)
    (hgr0 : gr 0 ≠ 0) (k m N : ℕ) (hN : m * p ^ (k + m + 3) ≤ N) (x : B)
    (hx : algebraMap B (Work.DSM4p.lvl Q hgr N) x ∈
      Ideal.span {((p : Work.DSM4p.lvl Q hgr N)) ^ m}) :
    Q.ϖ k * gr k * x ∈ Ideal.span {((p : B)) ^ m} := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · -- `m = 0`: the ideal is the whole ring
    subst hm0
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  -- the level `L` at which the `m = 1` step is applied
  set L : ℕ := k + m - 1 with hL
  have hL1 : L + 1 = k + m := by omega
  have hLN : p ^ (L + 3) ≤ N := by
    have hL3 : L + 3 = k + m + 2 := by omega
    rw [hL3]
    have h2 : p ^ (k + m + 2) ≤ p ^ (k + m + 3) :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    have h3 : p ^ (k + m + 3) ≤ m * p ^ (k + m + 3) := Nat.le_mul_of_pos_left _ hm
    exact le_trans h2 (le_trans h3 hN)
  -- the `m = 1` statement for `a := Q.ϖ (L+1) * gr (L+1)`
  have H : ∀ b : B, algebraMap B (lvl Q hgr N) b ∈ Ideal.span {(p : lvl Q hgr N)} →
      ∃ c : B, (Q.ϖ (L + 1) * gr (L + 1)) * b = (p : B) * c :=
    fun b hb => lvl_kernel_step Q hgr hgr0 L N hLN hb
  obtain ⟨c, hc⟩ := lvl_kernel_devissage_aux Q hgr N H m x hx
  -- `(Q.ϖ (L+1) * gr (L+1)) ^ p^m = Q.ϖ k * gr k`
  have hpow : (Q.ϖ (L + 1) * gr (L + 1)) ^ p ^ m = Q.ϖ k * gr k := by
    rw [mul_pow]
    have hv : Q.ϖ (L + 1) ^ p ^ m = Q.ϖ k := by
      rw [hL1]
      exact IsRootSystem.pow_pow Q.root k m
    have hg : gr (L + 1) ^ p ^ m = gr k := by
      rw [hL1]
      exact hgr.pow_pow k m
    rw [hv, hg]
  have hmle : m ≤ p ^ m :=
    le_of_lt (Nat.lt_pow_self (n := m) (a := p) (Fact.out : p.Prime).one_lt)
  refine Ideal.mem_span_singleton'.mpr
    ⟨(Q.ϖ (L + 1) * gr (L + 1)) ^ (p ^ m - m) * c, ?_⟩
  calc (Q.ϖ (L + 1) * gr (L + 1)) ^ (p ^ m - m) * c * (p : B) ^ m
      = (Q.ϖ (L + 1) * gr (L + 1)) ^ (p ^ m - m) * ((p : B) ^ m * c) := by ring
    _ = (Q.ϖ (L + 1) * gr (L + 1)) ^ (p ^ m - m) *
          ((Q.ϖ (L + 1) * gr (L + 1)) ^ m * x) := by rw [← hc]
    _ = (Q.ϖ (L + 1) * gr (L + 1)) ^ ((p ^ m - m) + m) * x := by rw [pow_add]; ring
    _ = (Q.ϖ (L + 1) * gr (L + 1)) ^ p ^ m * x := by rw [Nat.sub_add_cancel hmle]
    _ = Q.ϖ k * gr k * x := by rw [hpow]

end Work.DSM4p

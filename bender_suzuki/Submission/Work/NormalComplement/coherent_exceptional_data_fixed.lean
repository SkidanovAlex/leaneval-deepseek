import Mathlib
import Submission.Work.Coherence.Defs
import Submission.Work.CharCore.Defs
import Submission.Work.Coherence.NormIrr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Isaacs (7.13) — the exceptional characters of a coherent set, with the correct quantifier

This file contains a proof of Isaacs, *Character Theory of Finite Groups*, Lemma (7.13), i.e. of
`Work.NormalComplement.coherent_exceptional_data` **with the hypothesis `psi ∈ Irr W` placed
outside the biconditional**.

The statement requested at
`Submission/Work/NormalComplement/coherent_exceptional_data.lean` writes the last conjunct as

```
∀ psi : W → ℂ, psi ∈ Work.Coherence.Irr W →
  (∃ chi ∈ S, g chi = psi) ↔ ∃ theta ∈ ℤ[S]°, cfInner (tau' theta) psi ≠ 0
```

In Lean `→` binds *tighter* than `↔` (`→` has precedence 25, `↔` has precedence 20), so this
parses as

```
∀ psi, (psi ∈ Irr W → ∃ chi ∈ S, g chi = psi) ↔ (∃ theta ∈ ℤ[S]°, cfInner (tau' theta) psi ≠ 0)
```

which is **false**: for the zero function `psi = 0` (never an irreducible character, since
irreducible characters have positive degree at `1`) the left side is `True` while the right side is
`False` because `cfInner f 0 = 0`.  The present file proves the intended statement, with the
implication *outside* the biconditional; that is exactly Isaacs' "the image of `f` is the set of
`psi ∈ Irr W` with `[theta^tau, psi] ≠ 0` for some `theta ∈ ℤ[S]°`".

The mathematics is unchanged and is Isaacs' proof: `isometry_image_irr` (Schur orthogonality)
produces for each `chi ∈ S` a sign `s chi = ±1` with `tau' chi = s chi • psi chi` and `psi chi`
irreducible; since all `chi ∈ S` have the same degree `d ≠ 0` the differences `chi - chi'` lie in
`ℤ[S]°`, so `hdeg0` forces `tau' chi 1 = tau' chi' 1`, and the positivity of the degrees
(`irr_degree_pos`) then forces `s chi = s chi'`; injectivity follows from the isometry property,
and the description of the image from the orthonormality of `Irr W`.
-/

namespace Work.NormalComplement

open Classical

/-- **Signs are determined by degrees.**  Let `chi`, `psi` be irreducible complex characters of a
finite group `W` (so their degrees `chi 1`, `psi 1` are positive integers) and let `s`, `t ∈ {1,-1}`.
If `s * chi 1 = t * psi 1` then `s = t`. -/
theorem ced_deg_eq_sign {W : Type*} [Group W] [Fintype W] {chi psi : W → ℂ}
    (hchi : chi ∈ Work.Coherence.Irr W) (hpsi : psi ∈ Work.Coherence.Irr W)
    {s t : ℂ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (h : s * (chi 1) = t * (psi 1)) : s = t := by
  obtain ⟨n, hn, hchin⟩ := Work.Coherence.irr_degree_pos hchi
  obtain ⟨m, hm, hpsin⟩ := Work.Coherence.irr_degree_pos hpsi
  rw [hchin, hpsin] at h
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · rfl
  · exfalso
    have h' : (n : ℂ) = -(m : ℂ) := by simpa using h
    have hre : (n : ℝ) = -(m : ℝ) := by
      have := congrArg Complex.re h'; simpa using this
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    linarith
  · exfalso
    have h' : -(n : ℂ) = (m : ℂ) := by simpa using h
    have hre : -(n : ℝ) = (m : ℝ) := by
      have := congrArg Complex.re h'; simpa using this
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    linarith
  · rfl

/-- Two distinct elements of an orthonormal set are at squared distance `2`. -/
theorem ced_cfInner_sub_self_eq_two {G : Type*} [Group G] [Fintype G] {S : Finset (G → ℂ)}
    (hS : Work.Coherence.Orthonormal S) {x y : G → ℂ} (hx : x ∈ S) (hy : y ∈ S)
    (hne : x ≠ y) : Work.Coherence.cfInner (x - y) (x - y) = 2 := by
  rw [Work.Coherence.cfInner_sub_left, Work.Coherence.cfInner_sub_right,
      Work.Coherence.cfInner_sub_right,
      hS x hx x hx, hS y hy x hx, hS x hx y hy, hS y hy y hy]
  simp [hne, Ne.symm hne]
  norm_num

/-- **Injectivity of the exceptional-character map.**  If `S` is orthonormal and `tau` is an
isometry of `ℤ[S]`, then `chi ↦ eps • tau chi` is injective on `S` for `eps = ±1`. -/
theorem ced_injOn_smul_of_isometryOnAll {N W : Type*} [Group N] [Fintype N] [Group W] [Fintype W]
    {S : Finset (N → ℂ)} {tau : (N → ℂ) →ₗ[ℤ] (W → ℂ)}
    (horth : Work.Coherence.Orthonormal S) (hiso : Work.Coherence.IsometryOnAll S tau)
    {eps : ℂ} (heps : eps = 1 ∨ eps = -1) :
    Set.InjOn (fun chi => eps • tau chi) (S : Set (N → ℂ)) := by
  intro x hx y hy hxy
  by_contra hne
  have htau_eq : tau x = tau y := by
    rcases heps with h | h
    · rw [h] at hxy; simpa using hxy
    · rw [h] at hxy; simpa using hxy
  have hzero : tau (x - y) = 0 := by rw [map_sub, htau_eq, sub_self]
  have hmem : x - y ∈ Work.Coherence.ZSpan S :=
    AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hx) (Work.Coherence.self_mem_zSpan hy)
  have hnorm := hiso.inner_eq (x - y) hmem (x - y) hmem
  rw [hzero, Work.Coherence.cfInner_zero_left] at hnorm
  have h2 := ced_cfInner_sub_self_eq_two horth hx hy hne
  rw [h2] at hnorm
  norm_num at hnorm

/-- The difference of two elements of `S` of common degree `d` lies in `ℤ[S]°`. -/
theorem ced_sub_mem_zSpan0 {N : Type*} [Group N] [Fintype N] {S : Finset (N → ℂ)}
    {d : ℂ} (hd : ∀ chi ∈ S, chi 1 = d) {x y : N → ℂ} (hx : x ∈ S) (hy : y ∈ S) :
    x - y ∈ Work.Coherence.ZSpan0 S :=
  ⟨AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hx) (Work.Coherence.self_mem_zSpan hy),
   by simp [Pi.sub_apply, hd x hx, hd y hy]⟩

/-- **Isaacs (7.13), the uniform sign.**  Under the hypotheses of the theorem, the sign `s` with
`s • tau' chi ∈ Irr W` is independent of `chi ∈ S`. -/
theorem ced_exists_eps_irr {N W : Type*} [Group N] [Fintype N] [Group W] [Fintype W]
    {S : Finset (N → ℂ)} {tau tau' : (N → ℂ) →ₗ[ℤ] (W → ℂ)}
    (hcard : 2 ≤ S.card)
    (hS : ∀ chi ∈ S, chi ∈ Work.Coherence.Irr N)
    (hdeg : ∃ d : ℂ, d ≠ 0 ∧ ∀ chi ∈ S, chi 1 = d)
    (hdeg0 : ∀ alpha ∈ Work.Coherence.ZSpan0 S, tau alpha 1 = 0)
    (hagree : ∀ alpha ∈ Work.Coherence.ZSpan0 S, tau' alpha = tau alpha)
    (hiso : Work.Coherence.IsometryOnAll S tau')
    (hvchar : ∀ chi ∈ S, Work.Coherence.IsVChar (tau' chi)) :
    ∃ eps : ℂ, (eps = 1 ∨ eps = -1) ∧ ∀ chi ∈ S, eps • tau' chi ∈ Work.Coherence.Irr W := by
  obtain ⟨d, hdne, hd⟩ := hdeg
  have horth : Work.Coherence.Orthonormal S :=
    Work.Coherence.irr_orthonormal_finset (fun x hx => hS x hx)
  have hpos : 0 < S.card := by omega
  obtain ⟨chi0, hchi0⟩ := Finset.card_pos.mp hpos
  have hex : ∀ chi ∈ S, ∃ (s : ℂ) (psi : W → ℂ),
      (s = 1 ∨ s = -1) ∧ psi ∈ Work.Coherence.Irr W ∧ tau' chi = s • psi := by
    intro chi hchi
    obtain ⟨psi, hpsi, hcase⟩ :=
      Work.Coherence.isometry_image_irr horth hiso hchi (hvchar chi hchi)
    rcases hcase with h | h
    · exact ⟨1, psi, Or.inl rfl, hpsi, by rw [h]; simp⟩
    · exact ⟨-1, psi, Or.inr rfl, hpsi, by rw [h]; simp⟩
  obtain ⟨s0, psi0, hs0, hpsi0, htau0⟩ := hex chi0 hchi0
  refine ⟨s0, hs0, ?_⟩
  intro chi hchi
  obtain ⟨s, psi, hs, hpsi, htau⟩ := hex chi hchi
  have hmem : chi - chi0 ∈ Work.Coherence.ZSpan0 S := ced_sub_mem_zSpan0 hd hchi hchi0
  have hdegeq : tau' chi 1 = tau' chi0 1 := by
    have h1 : tau' (chi - chi0) = tau (chi - chi0) := hagree (chi - chi0) hmem
    have h2 : (tau' (chi - chi0)) 1 = 0 := by
      rw [h1]; exact hdeg0 (chi - chi0) hmem
    rw [map_sub, Pi.sub_apply] at h2
    exact sub_eq_zero.mp h2
  have hsign : s = s0 := by
    refine ced_deg_eq_sign hpsi hpsi0 hs hs0 ?_
    have e1 : tau' chi 1 = s * (psi 1) := by rw [htau, Pi.smul_apply, smul_eq_mul]
    have e2 : tau' chi0 1 = s0 * (psi0 1) := by rw [htau0, Pi.smul_apply, smul_eq_mul]
    rw [e1, e2] at hdegeq
    exact hdegeq
  rw [hsign] at htau
  rw [htau]
  have hsq : s0 • (s0 • psi) = psi := by
    rcases hs0 with h | h <;> rw [h] <;> simp
  rw [hsq]
  exact hpsi

/-- **Isaacs (7.13), the image of the exceptional-character map.**  For an irreducible `psi` of
`W`, `psi` is one of the `eps • tau' chi` (`chi ∈ S`) if and only if it pairs non-trivially with
`tau' theta` for some `theta ∈ ℤ[S]°`. -/
theorem ced_image_iff {N W : Type*} [Group N] [Fintype N] [Group W] [Fintype W]
    {S : Finset (N → ℂ)} {tau tau' : (N → ℂ) →ₗ[ℤ] (W → ℂ)} {eps : ℂ}
    (hcard : 2 ≤ S.card)
    (hS : ∀ chi ∈ S, chi ∈ Work.Coherence.Irr N)
    (hdeg : ∃ d : ℂ, d ≠ 0 ∧ ∀ chi ∈ S, chi 1 = d)
    (hdeg0 : ∀ alpha ∈ Work.Coherence.ZSpan0 S, tau alpha 1 = 0)
    (hagree : ∀ alpha ∈ Work.Coherence.ZSpan0 S, tau' alpha = tau alpha)
    (heps : eps = 1 ∨ eps = -1)
    (hIrr : ∀ chi ∈ S, eps • tau' chi ∈ Work.Coherence.Irr W)
    (hinj : Set.InjOn (fun chi => eps • tau' chi) (S : Set (N → ℂ))) :
    ∀ psi : W → ℂ, psi ∈ Work.Coherence.Irr W →
      ((∃ chi ∈ S, eps • tau' chi = psi) ↔
        ∃ theta ∈ Work.Coherence.ZSpan0 S,
          Work.Coherence.cfInner (tau' theta) psi ≠ 0) := by
  intro psi hpsi
  obtain ⟨d, hdne, hd⟩ := hdeg
  have heps_sq : eps * eps = 1 := by rcases heps with h | h <;> rw [h] <;> norm_num
  have heps_ne : eps ≠ 0 := by rcases heps with h | h <;> rw [h] <;> norm_num
  have htau_eq : ∀ chi : N → ℂ, tau' chi = eps • (eps • tau' chi) := by
    intro chi; rw [smul_smul, heps_sq, one_smul]
  constructor
  · -- forward: `psi = eps • tau' chi` pairs with `tau' (chi - chi0)`
    rintro ⟨chi, hchi, hchi_psi⟩
    obtain ⟨chi0, hchi0, hne0⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) chi
    refine ⟨chi - chi0, ced_sub_mem_zSpan0 hd hchi hchi0, ?_⟩
    have hpsi0_irr : eps • tau' chi0 ∈ Work.Coherence.Irr W := hIrr chi0 hchi0
    have hne' : eps • tau' chi0 ≠ psi := by
      intro h
      exact hne0 (hinj hchi0 hchi (h.trans hchi_psi.symm))
    have hcalc : Work.Coherence.cfInner (tau' (chi - chi0)) psi = eps := by
      have hτχ : tau' chi = eps • psi := by
        have h' : eps • (eps • tau' chi) = eps • psi := by rw [hchi_psi]
        rwa [← htau_eq chi] at h'
      have h1 : tau' (chi - chi0) = eps • (psi - eps • tau' chi0) := by
        conv_lhs => rw [map_sub, hτχ, htau_eq chi0]
        rw [smul_sub]
      rw [h1, Work.Coherence.cfInner_smul_left, Work.Coherence.cfInner_sub_left,
          Work.Coherence.irr_cfInner hpsi hpsi, if_pos rfl,
          Work.Coherence.irr_cfInner hpsi0_irr hpsi, if_neg hne']
      ring
    rw [hcalc]; exact heps_ne
  · -- backward: expand `theta` in the basis `S` and extract a non-zero term
    rintro ⟨theta, htheta, hinner⟩
    obtain ⟨c, hc⟩ := Work.Coherence.mem_zSpan.mp (Work.Coherence.zSpan0_le_zSpan S htheta)
    have hmap : tau' theta = ∑ x : S, (c x : ℂ) • tau' (x : N → ℂ) := by
      rw [hc, map_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Int.cast_smul_eq_zsmul, map_zsmul]
    have hcf : Work.Coherence.cfInner (tau' theta) psi =
        ∑ x : S, (c x : ℂ) * eps * (if eps • tau' (x : N → ℂ) = psi then 1 else 0) := by
      rw [hmap, Work.Coherence.cfInner_sum_left]
      refine Finset.sum_congr rfl fun x _ => ?_
      conv_lhs => rw [Work.Coherence.cfInner_smul_left, htau_eq (x : N → ℂ),
        Work.Coherence.cfInner_smul_left]
      rw [Work.Coherence.irr_cfInner (hIrr (x : N → ℂ) x.2) hpsi]
      ring
    obtain ⟨x, -, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [← hcf]; exact hinner)
    refine ⟨(x : N → ℂ), x.2, ?_⟩
    by_contra hcon
    rw [if_neg hcon] at hxne
    simp at hxne

/-- **Isaacs (7.13): the exceptional characters of a coherent set** (with the hypothesis
`psi ∈ Irr W` placed outside the biconditional, as in the source). -/
theorem coherent_exceptional_data' {N W : Type*} [Group N] [Fintype N] [Group W] [Fintype W]
    {S : Finset (N → ℂ)} {tau : (N → ℂ) →ₗ[ℤ] (W → ℂ)}
    (hcard : 2 ≤ S.card)
    (hS : ∀ chi ∈ S, chi ∈ Work.Coherence.Irr N)
    (hdeg : ∃ d : ℂ, d ≠ 0 ∧ ∀ chi ∈ S, chi 1 = d)
    (hdeg0 : ∀ alpha ∈ Work.Coherence.ZSpan0 S, tau alpha 1 = 0)
    (hcoh : Work.Coherence.Coherent S tau) :
    ∃ (tau' : (N → ℂ) →ₗ[ℤ] (W → ℂ)) (g : (N → ℂ) → (W → ℂ)) (eps : ℂ),
      (∀ alpha ∈ Work.Coherence.ZSpan0 S, tau' alpha = tau alpha) ∧
      Work.Coherence.IsometryOnAll S tau' ∧
      (∀ chi ∈ S, Work.Coherence.IsVChar (tau' chi)) ∧
      (eps = 1 ∨ eps = -1) ∧
      (∀ chi ∈ S, g chi = eps • tau' chi) ∧
      (∀ chi ∈ S, g chi ∈ Work.Coherence.Irr W) ∧
      (Set.InjOn g (S : Set (N → ℂ))) ∧
      (∀ psi : W → ℂ, psi ∈ Work.Coherence.Irr W →
        ((∃ chi ∈ S, g chi = psi) ↔
          ∃ theta ∈ Work.Coherence.ZSpan0 S,
            Work.Coherence.cfInner (tau' theta) psi ≠ 0)) := by
  obtain ⟨tau', hagree, hiso, hvchar⟩ := hcoh
  have horth : Work.Coherence.Orthonormal S :=
    Work.Coherence.irr_orthonormal_finset (fun x hx => hS x hx)
  obtain ⟨eps, heps, hIrr⟩ := ced_exists_eps_irr hcard hS hdeg hdeg0 hagree hiso hvchar
  have hinj : Set.InjOn (fun chi => eps • tau' chi) (S : Set (N → ℂ)) :=
    ced_injOn_smul_of_isometryOnAll horth hiso heps
  have himg := ced_image_iff hcard hS hdeg hdeg0 hagree heps hIrr hinj
  exact ⟨tau', fun chi => eps • tau' chi, eps, hagree, hiso, hvchar, heps,
    fun chi hchi => rfl, hIrr, hinj, himg⟩

/-!
## Certificates for the mis-statement of the requested lemma

The requested lemma writes its final conjunct as

```
∀ psi : W → ℂ, psi ∈ Work.Coherence.Irr W →
  (∃ chi ∈ S, g chi = psi) ↔ ∃ theta ∈ ℤ[S]°, cfInner (tau' theta) psi ≠ 0
```

Since `→` binds tighter than `↔`, Lean reads the hypothesis `psi ∈ Irr W` as the *left-hand side of
the biconditional*:

```
∀ psi, (psi ∈ Irr W → ∃ chi ∈ S, g chi = psi) ↔ (∃ theta ∈ ℤ[S]°, cfInner (tau' theta) psi ≠ 0)
```

The following two lemmas certify that this is false (so the requested lemma is unprovable): the
second shows that the conjunct is unsatisfiable for *every* `W`, `S`, `g`, `tau'`, using `psi = 0`;
the first records that `0` is indeed not an irreducible character.
-/

/-- The zero function is not an irreducible character of a finite group: irreducible characters
have positive degree at `1` (`irr_degree_pos`). -/
theorem ced_zero_not_mem_Irr {W : Type*} [Group W] [Fintype W] :
    (0 : W → ℂ) ∉ Work.Coherence.Irr W := by
  intro h
  obtain ⟨n, hn, h1⟩ := Work.Coherence.irr_degree_pos h
  have h2 : (n : ℂ) = 0 := by rw [← h1]; simp
  exact hn.ne' (by exact_mod_cast h2)

/-- **The final conjunct of the requested statement is unsatisfiable.**  As literally parsed, it
asserts for `psi = 0` that `(0 ∈ Irr W → _) ↔ (∃ theta ∈ ℤ[S]°, cfInner (tau' theta) 0 ≠ 0)`, i.e.
`True ↔ False` (`cfInner f 0 = 0` for all `f`). -/
theorem ced_lastConjunct_false {W : Type*} [Group W] [Fintype W] (S : Finset (W → ℂ))
    (g : (W → ℂ) → (W → ℂ)) (tau' : (W → ℂ) →ₗ[ℤ] (W → ℂ)) :
    ¬ (∀ psi : W → ℂ,
        (psi ∈ Work.Coherence.Irr W → ∃ chi ∈ S, g chi = psi) ↔
          ∃ theta ∈ Work.Coherence.ZSpan0 S,
            Work.Coherence.cfInner (tau' theta) psi ≠ 0) := by
  intro h
  have h0 := (h 0).mp (fun hmem => absurd hmem ced_zero_not_mem_Irr)
  obtain ⟨theta, -, htheta⟩ := h0
  exact htheta (by simp)

/-- **The hypotheses of the requested lemma are satisfiable.**  If a finite group `N` has two
distinct irreducible characters `chi1 ≠ chi2` of common non-zero degree, then taking `W := N`,
`S := {chi1, chi2}` and `tau := LinearMap.id` satisfies all five hypotheses of the requested
lemma (`hcard`, `hS`, `hdeg`, `hdeg0`, `hcoh`): `|S| = 2`; both are irreducible; both have degree
`chi1 1 ≠ 0`; `tau = id` maps `ℤ[S]°` (degree-zero in, degree-zero out) to degree-zero functions;
and `S` is coherent for `id` with the extension `tau' = id`.

The hypothesis is met by any group of order `2` (whose two irreducible characters both have degree
`1`), so the requested lemma is not vacuously true, and combined with `ced_lastConjunct_false` it
is false. -/
theorem ced_model_of_two_irr {N : Type*} [Group N] [Fintype N]
    {chi1 chi2 : N → ℂ} (h1 : chi1 ∈ Work.Coherence.Irr N)
    (h2 : chi2 ∈ Work.Coherence.Irr N) (hne : chi1 ≠ chi2) (hdeg : chi1 1 = chi2 1)
    (hne0 : chi1 1 ≠ 0) :
    2 ≤ ({chi1, chi2} : Finset (N → ℂ)).card ∧
      (∀ chi ∈ ({chi1, chi2} : Finset (N → ℂ)), chi ∈ Work.Coherence.Irr N) ∧
      (∃ d : ℂ, d ≠ 0 ∧ ∀ chi ∈ ({chi1, chi2} : Finset (N → ℂ)), chi 1 = d) ∧
      (∀ alpha ∈ Work.Coherence.ZSpan0 ({chi1, chi2} : Finset (N → ℂ)),
        (LinearMap.id : (N → ℂ) →ₗ[ℤ] (N → ℂ)) alpha 1 = 0) ∧
      Work.Coherence.Coherent ({chi1, chi2} : Finset (N → ℂ))
        (LinearMap.id : (N → ℂ) →ₗ[ℤ] (N → ℂ)) := by
  have hmem : ∀ chi ∈ ({chi1, chi2} : Finset (N → ℂ)), chi ∈ Work.Coherence.Irr N := by
    intro chi hchi
    rcases Finset.mem_insert.mp hchi with h | h
    · rwa [h]
    · rw [Finset.mem_singleton.mp h]; exact h2
  refine ⟨?_, hmem, ⟨chi1 1, hne0, ?_⟩, ?_, ?_⟩
  · have hcard : ({chi1, chi2} : Finset (N → ℂ)).card = 2 := Finset.card_pair hne
    omega
  · intro chi hchi
    rcases Finset.mem_insert.mp hchi with h | h
    · rw [h]
    · rw [Finset.mem_singleton.mp h]; exact hdeg.symm
  · intro alpha halpha
    simpa using halpha.2
  · refine ⟨LinearMap.id, fun _ _ => rfl, ⟨fun _ _ _ _ => rfl⟩, ?_⟩
    intro chi hchi
    exact Work.Coherence.isVChar_of_mem_Irr (hmem chi hchi)

end Work.NormalComplement

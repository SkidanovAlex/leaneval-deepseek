import Submission.ZagierHoffmanProof.AbpDescentRestrict



import Submission.Commons.RingTheory.Polynomial.fixed_of_map_mul_eq

/-!
# The `K^{perf}` → `K` descent, second half: the ABP criterion applied to the restricted motive

This file completes the descent (Dac §5.2 / Chang Prop. 4.3.1).  `descent_relation` takes the
coefficient vector `ρ` (of a `K^{perf}`-linear relation between the top-weight values, normalised by
`ρ (some (descT t₀ ht₀)) = 1`) and produces the ABP row vector `P` with `P·ψ = 0` and `P(θ) = ρ`,
then the second relation of Dac §5.2 with the sparsification `descent_sparse`, then
`descent_vanishing` to kill the top-weight coefficients, and finally
`Commons.RingTheory.Polynomial.fixed_of_map_mul_eq` to conclude `ρ (some u) ∈ ambK F` for every
top-weight `u ≠ descT t₀ ht₀` — i.e. the coefficients of the relation are `K`-rational.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Matrix Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-- The proof that `[]` is an index of the restricted motive. -/
noncomputable def descNil {S : Finset (List (ℕ × Polynomial (Ambient F)))} {w₀ : ℕ}
    {t₀ : ↥(tmI S)} (ht₀ : tmWeight t₀.1 = w₀) :
    ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI (descS S w₀) :=
  mem_tmI_descS.mpr ⟨t₀, ht₀, 0, by omega, by simp⟩

/-- The first column of the rigid analytic trivialisation of the restricted motive. -/
noncomputable def descPsi {S : Finset (List (ℕ × Polynomial (Ambient F)))} (w₀ : ℕ)
    (ω : PowerSeries (Ambient F)) {t₀ : ↥(tmI S)} (ht₀ : tmWeight t₀.1 = w₀) :
    Option ↥(tmI (descS S w₀)) → PowerSeries (Ambient F) :=
  tmPsiCol F ω w₀ (descS S w₀) (fun _ => (0 : Polynomial (Ambient F))) (descNil (F := F) ht₀)

theorem descent_relation {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
    (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F)
    (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ m, (y.2).coeff m ∈ ambA F 0)
    {w₀ : ℕ} {t₀ : ↥(tmI S)} (ht₀ : tmWeight t₀.1 = w₀)
    (hind : LinearIndependent (ambKperf F)
      (fun t : {t : ↥(tmI S) // tmWeight t.1 = w₀ ∧ t ≠ t₀} =>
        evalSeriesGen (tmL (Nat.card F) ω t.1.1) (ambTheta F)))
    {ρ : Option ↥(tmI (descS S w₀)) → Ambient F}
    (hρmem : ∀ i, ρ i ∈ ambKperf F) (hρ0 : ρ ≠ 0)
    (hρtop : ρ (some (descT (F := F) (w₀ := w₀) t₀ ht₀)) = 1)
    (hval : dotProduct ρ (fun i => evalSeriesGen (descPsi (F := F) w₀ ω ht₀ i)
      (ambTheta F)) = 0) :
    ∀ u : ↥(tmI (descS S w₀)), tmWeight u.1 = w₀ →
      u ≠ descT (F := F) (w₀ := w₀) t₀ ht₀ → ρ (some u) ∈ ambK F := by
  classical
  haveI : FrobPow (Ambient F) (Nat.card F) := frobPow_ambient F
  -- hypotheses for the restricted motive
  have hsm'' : ∀ s ∈ descS S w₀, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))) :=
    descS_isSmall (S := S) (w₀ := w₀) hsm
  have hSse'' : ∀ s ∈ descS S w₀, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))) :=
    descS_superEntire (S := S) (w₀ := w₀) hSse
  have hne'' : ∀ s ∈ descS S w₀, s ≠ [] := fun s hs => descS_ne_nil hs
  have hw'' : ∀ s ∈ descS S w₀, tmWeight s = w₀ := fun s hs => descS_weight hs
  have hcf'' : ∀ s ∈ descS S w₀, frobTwist (R := Ambient F) (p := Nat.card F) 1
      (((fun _ => (0 : Polynomial (Ambient F))) s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = (((fun _ => (0 : Polynomial (Ambient F))) s : Polynomial (Ambient F))
        : PowerSeries (Ambient F)) := by
    intro s _
    rw [Polynomial.coe_zero, frobTwist_zero]
  have h0'' : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI (descS S w₀) := descNil (F := F) ht₀
  have hA'' : ∀ i j m, (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
      (fun _ => (0 : Polynomial (Ambient F))) i j).coeff m ∈ ambA F 0 :=
    tmAOpt_descS_coeff_mem_ambA0 (S := S) (w₀ := w₀) hQmem
  -- the level of `ρ`
  obtain ⟨ν₀, hν₀⟩ := exists_ratLevelF_forall_of_mem_ambKperf (F := F)
    (Finset.univ : Finset (Option ↥(tmI (descS S w₀)))) ρ (fun i _ => hρmem i)
  set ν : ℕ := max 1 ν₀ with hνdef
  have hρlev : ∀ i, ρ i ∈ ratLevelF (F := F) ν := fun i =>
    ratLevelF_mono (F := F) (le_trans (le_max_right 1 ν₀) (le_of_eq hνdef.symm)) (hν₀ i (Finset.mem_univ i))
  -- the vanishing matrix
  obtain ⟨ϑ, hϑmem, hϑli, hϑvec⟩ := exists_aux_theta (F := F) ν hρ0 hρlev
  -- the criterion
  have hℓ : 2 ≤ Fintype.card (Option ↥(tmI (descS S w₀))) := by
    rw [Fintype.card_option]
    exact Nat.succ_le_succ (Fintype.card_pos_iff.mpr ⟨⟨[], h0''⟩⟩)
  have hJ : Fintype.card (Fin (Fintype.card (Option ↥(tmI (descS S w₀))) - 1))
      = Fintype.card (Option ↥(tmI (descS S w₀))) - 1 := Fintype.card_fin _
  have hΦmem : ∀ i j m, (tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀
      (descS S w₀) (fun _ => (0 : Polynomial (Ambient F)))) hA'' i j).coeff m ∈ ambA F ν :=
    fun i j m => ambA_mono F (by rw [hνdef]; exact le_max_left 1 ν₀)
      (tmPhi_coeff_mem F _ hA'' i j m)
  have hdet : (tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
      (fun _ => (0 : Polynomial (Ambient F)))) hA'').det
      = Polynomial.C (1 : Ambient F) * (Polynomial.X - Polynomial.C (ambTheta F))
        ^ (∑ t : ↥(tmI (descS S w₀)), (w₀ - tmWeight t.1)) := by
    rw [det_tmPhi F w₀ (descS S w₀) (fun _ => 0) hA'']
    simp
  obtain ⟨P, hPψ, hPθ, hPmem⟩ :=
    ABP_criterion_of_fintype_kperf (F := F) (ν := ν) (ι := Option ↥(tmI (descS S w₀)))
      (J := Fin (Fintype.card (Option ↥(tmI (descS S w₀))) - 1)) hℓ hJ hΦmem hϑmem
      hγ0 hγ
      (tmPsiCol_superEntire F (ω := ω) hγ0 hγ harch hq hω hωse hsm'' hSse'' h0'')
      (tmPsiCol_functional F (w := w₀) hγ harch hq hω hωfe hw'' hcf'' hsm'' hne'' h0'' hA'')
      hϑli hϑvec hρ0 hρmem hval one_ne_zero hdet
  -- ## Step 1: the second relation and the sparsification
  -- the functional equation in the form required by `tm_second_relation`
  have hfe : descPsi (F := F) w₀ ω ht₀
      = ((coeHom (K := Ambient F)).mapMatrix
            (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
              (fun _ => (0 : Polynomial (Ambient F)))))
        *ᵥ (frobTwistVec (q := Nat.card F) 1 (descPsi (F := F) w₀ ω ht₀)) := by
    have h := tmPsiCol_functional F (w := w₀) (ω := ω) hγ harch hq hω hωfe hw'' hcf'' hsm'' hne''
      h0'' hA''
    rw [tmPhi_twist_mat F _ hA''] at h
    simpa only [descPsi] using h
  -- the distinguished coordinate
  let t' : ↥(tmI (descS S w₀)) := descT (F := F) (w₀ := w₀) t₀ ht₀
  have ht' : tmWeight t'.1 = w₀ := ht₀
  have hcol : ∀ i : Option ↥(tmI (descS S w₀)),
      tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
        (fun _ => (0 : Polynomial (Ambient F))) i (some t') = if i = some t' then 1 else 0 :=
    tmAOpt_descS_column (S := S) (w₀ := w₀) hpos ht'
  obtain ⟨hBrel, hBt'⟩ := tm_second_relation (q := Nat.card F) (A := tmAOpt (K := Ambient F)
      (Nat.card F) (ambTheta F) w₀ (descS S w₀) (fun _ => (0 : Polynomial (Ambient F))))
    (ψ := descPsi (F := F) w₀ ω ht₀) hfe hPψ t' hcol
  -- rewrite the relation into the shape required by `descent_sparse`
  have hψnone : descPsi (F := F) w₀ ω ht₀ none = 0 := by
    rw [descPsi, tmPsiCol_none, tmF_nil]
    simp
  have hψsome : ∀ t : ↥(tmI (descS S w₀)),
      descPsi (F := F) w₀ ω ht₀ (some t)
        = tmL (Nat.card F) ω t.1 * ω ^ (w₀ - tmWeight t.1) := fun t => by
    rw [descPsi]
    exact tmPsiCol_some F ω w₀ (descS S w₀) (fun _ => (0 : Polynomial (Ambient F)))
      (descNil (F := F) ht₀) t
  have heq : (∑ t : ↥(tmI (descS S w₀)), coeHom (K := Ambient F)
        (P t' * polyTwist (q := Nat.card F) 1 (P t)
          - polyTwist (q := Nat.card F) 1 (P t')
            * ∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
                (fun _ => (0 : Polynomial (Ambient F))) i t))
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1)))
      = ∑ j : Option ↥(tmI (descS S w₀)), coeHom (K := Ambient F)
          (P t' * polyTwist (q := Nat.card F) 1 (P j)
            - polyTwist (q := Nat.card F) 1 (P t')
              * ∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
                  (fun _ => (0 : Polynomial (Ambient F))) i j))
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (descPsi (F := F) w₀ ω ht₀ j) := by
    rw [Fintype.sum_option]
    rw [show coeHom (K := Ambient F) (P t' * polyTwist (q := Nat.card F) 1 (P none)
          - polyTwist (q := Nat.card F) 1 (P t')
            * ∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
                (fun _ => (0 : Polynomial (Ambient F))) i none))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (descPsi (F := F) w₀ ω ht₀ none) = 0 by
      rw [hψnone, frobTwist_zero, mul_zero]]
    rw [zero_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hψsome t, frobTwist_mul, frobTwist_pow]
  have hBrel'' : (∑ t : ↥(tmI (descS S w₀)), coeHom (K := Ambient F)
        (P t' * polyTwist (q := Nat.card F) 1 (P t)
          - polyTwist (q := Nat.card F) 1 (P t')
            * ∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
                (fun _ => (0 : Polynomial (Ambient F))) i t))
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w₀ - tmWeight t.1))) = 0 := by
    rw [heq, hBrel]
  -- the side hypotheses of `descent_sparse`
  have hΩ1 : ∀ j : ℕ, 2 ≤ j →
      evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
        ((ambTheta F) ^ (Nat.card F) ^ j) = 0 := by
    intro j hj
    have hq1 : ((ambTheta F) ^ (Nat.card F ^ (j - 1))) ^ (Nat.card F ^ 1)
        = (ambTheta F) ^ (Nat.card F) ^ j := by
      rw [pow_one, ← pow_mul]
      congr 1
      conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ j by omega)]
      rw [pow_succ]
    have h := evalSeriesGen_frobTwist hγ harch (Nat.card F) hωse
      ((ambTheta F) ^ (Nat.card F ^ (j - 1))) 1
    rw [hq1] at h
    have h2 : evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ (j - 1))) = 0 := hc (j - 1) (by omega)
    rw [h2] at h
    have hz : (0 : Ambient F) ^ (Nat.card F ^ 1) = 0 :=
      zero_pow (pow_ne_zero 1 (FrobPow.ne_zero (Ambient F) (q := Nat.card F)))
    rw [hz] at h
    exact h
  have hLse : ∀ t : ↥(tmI (descS S w₀)), GSuperEntire γ (tmL (Nat.card F) ω t.1) :=
    fun t => gSuperEntire_tmL F hγ harch hq hω hωse hsm'' hSse'' t
  have hMZ : ∀ (t : ↥(tmI (descS S w₀))) (k : ℕ),
      evalSeriesGen (tmL (Nat.card F) ω t.1) ((ambTheta F) ^ (Nat.card F ^ k))
        = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ k) :=
    fun t k => tmL_frobenius_pow_mem (F := F) (S := descS S w₀) hγ0 hγ harch hq hω hωse
      hsm'' hSse'' (fun u y hy => tmI_descS_pos (S := S) (w₀ := w₀) hpos u hy) (fun k hk => hc k hk) t k
  have hsparse := descent_sparse (F := F) (γ := γ) (w₀ := w₀) (ω := ω) (S := descS S w₀)
    (B := fun t => P t' * polyTwist (q := Nat.card F) 1 (P t)
      - polyTwist (q := Nat.card F) 1 (P t')
        * ∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
            (fun _ => (0 : Polynomial (Ambient F))) i t))
    hγ0 hγ harch hq hωse hΩ1 hLse hMZ (fun t => tmI_descS_weight_le (S := S) (w₀ := w₀) t)
    (by simpa using hBrel'')
  -- ## Step 2: the coefficients of `B̃` lie in `K^{perf}`, and the vanishing step
  have hcoeff : ∀ (i j : Option ↥(tmI (descS S w₀))) (m : ℕ),
      ((tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
        (fun _ => (0 : Polynomial (Ambient F)))) i j).coeff m ∈ ambKperf F :=
    fun i j m => ambA_subset_ambKperf F 0 (hA'' i j m)
  have hTwist : ∀ {p : Polynomial (Ambient F)}, (∀ m, p.coeff m ∈ ambKperf F) →
      ∀ m, (polyTwist (q := Nat.card F) 1 p).coeff m ∈ ambKperf F := by
    intro p hp m
    rw [polyTwist, polyTwistHom_apply, Polynomial.coeff_map, frobPowHom_apply]
    exact Subfield.pow_mem _ (hp m) _
  have hSum : ∀ (j : Option ↥(tmI (descS S w₀))) (m : ℕ),
      ((∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
        (fun _ => (0 : Polynomial (Ambient F))) i j))).coeff m ∈ ambKperf F := by
    intro j m
    rw [Polynomial.finsetSum_coeff]
    refine Subfield.sum_mem _ fun i _ => ?_
    rw [Polynomial.coeff_mul]
    exact Subfield.sum_mem _ fun x _ => Subfield.mul_mem _ (hPmem i x.1) (hcoeff i j x.2)
  have hBmem : ∀ u : ↥(tmI (descS S w₀)), ∀ m,
      ((P (some t') * polyTwist (q := Nat.card F) 1 (P (some u))
      - polyTwist (q := Nat.card F) 1 (P (some t'))
        * ∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
            (fun _ => (0 : Polynomial (Ambient F))) i (some u)))).coeff m ∈ ambKperf F := by
    intro u m
    rw [Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_mul]
    refine Subfield.sub_mem _ ?_ ?_
    · exact Subfield.sum_mem _ fun x _ =>
        Subfield.mul_mem _ (hPmem (some t') x.1) (hTwist (hPmem (some u)) x.2)
    · exact Subfield.sum_mem _ fun x _ =>
        Subfield.mul_mem _ (hTwist (hPmem (some t')) x.1) (hSum (some u) x.2)
  have hrel' : ∀ N : ℕ, 2 ≤ N → (∑ u ∈ descV (F := F) (S := S) w₀,
      ((fun u => P (some t') * polyTwist (q := Nat.card F) 1 (P (some u))
        - polyTwist (q := Nat.card F) 1 (P (some t'))
          * ∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
              (fun _ => (0 : Polynomial (Ambient F))) i (some u))) u).eval
        ((ambTheta F) ^ (Nat.card F ^ N))
      * (descZ (F := F) (S := S) w₀ ω u) ^ (Nat.card F ^ N)) = 0 := by
    intro N hN
    simp only [descV, descZ_def]
    exact hsparse N hN
  have hBzero := descent_vanishing (F := F) (ω := ω) hq hpos ht₀ hind
    (B := fun u => P (some t') * polyTwist (q := Nat.card F) 1 (P (some u))
      - polyTwist (q := Nat.card F) 1 (P (some t'))
        * ∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
            (fun _ => (0 : Polynomial (Ambient F))) i (some u)))
    hBmem (by simpa only [] using hBt') hrel'
  -- ## Step 3: the rationality of the coefficients
  -- the ring isomorphism `F ≃+* ambF F`
  let ψ : F →+* ↥(ambF F) := (ambCoeff F).codRestrict (ambF F).toSubring
    (fun x => ambCoeff_mem_ambF F x)
  have hψval : ∀ x : F, ((ψ x : ↥(ambF F)) : Ambient F) = ambCoeff F x := fun x => rfl
  have hψinj : Function.Injective ψ := by
    intro x y h
    have h1 : ((ψ x : ↥(ambF F)) : Ambient F) = ((ψ y : ↥(ambF F)) : Ambient F) :=
      congrArg Subtype.val h
    rw [hψval, hψval] at h1
    exact RingHom.injective (ambCoeff F) h1
  have hψsurj : Function.Surjective ψ := by
    intro z
    have hz : (z : Ambient F) ∈ Set.range (ambCoeff F) := by
      rw [range_ambCoeff_eq_ambF]; exact z.2
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext (by rw [hψval]; exact hx)⟩
  let φ : F ≃+* ↥(ambF F) := RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hcoe : ∀ x : F, (((φ x : ↥(ambF F)) : Ambient F)) = algebraMap F (Ambient F) x := by
    intro x
    show ((ψ x : ↥(ambF F)) : Ambient F) = algebraMap F (Ambient F) x
    rw [hψval, algebraMap_ambient_eq]
  have hcomp : (algebraMap F (Ambient F)).comp (φ.symm : ↥(ambF F) →+* F) = (ambF F).subtype := by
    ext x
    show algebraMap F (Ambient F) (φ.symm x) = ((x : ↥(ambF F)) : Ambient F)
    rw [← hcoe (φ.symm x), φ.apply_symm_apply]
  -- a nonzero polynomial over `ambF F` does not vanish at `θ`
  have hQ'ne : ∀ {q : Polynomial (ambF F)}, q ≠ 0 →
      (q.map (ambF F).subtype).eval (ambTheta F) ≠ 0 := by
    intro q hq h0
    have hmap : q.map (ambF F).subtype
        = (q.map (φ.symm : ↥(ambF F) →+* F)).map (algebraMap F (Ambient F)) := by
      rw [Polynomial.map_map, hcomp]
    have h0' : (q.map (φ.symm : ↥(ambF F) →+* F)).eval₂ (algebraMap F (Ambient F))
        (ambTheta F) = 0 := by
      rw [hmap, Polynomial.eval_map] at h0
      exact h0
    have hq' : q.map (φ.symm : ↥(ambF F) →+* F) ≠ 0 := fun h =>
      hq ((Polynomial.map_eq_zero_iff φ.symm.injective).mp h)
    exact hq' (ambTheta_transcendental F _ h0')
  -- the column of `A` at `some u` is `e_{some u}`
  intro u hu hune
  have hcolu : ∀ i : Option ↥(tmI (descS S w₀)),
      tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
        (fun _ => (0 : Polynomial (Ambient F))) i (some u) = if i = some u then 1 else 0 :=
    tmAOpt_descS_column (S := S) (w₀ := w₀) hpos hu
  have hPA : (∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w₀ (descS S w₀)
      (fun _ => (0 : Polynomial (Ambient F))) i (some u))) = P (some u) := by
    rw [Finset.sum_eq_single (some u)]
    · rw [hcolu (some u), if_pos rfl, mul_one]
    · intro i _ hi
      rw [hcolu i, if_neg hi, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (some u)) h
  -- `B̃ (some u) = 0` in the required form
  have hB0 : P (some t') * polyTwist (q := Nat.card F) 1 (P (some u))
      = polyTwist (q := Nat.card F) 1 (P (some t')) * P (some u) := by
    have h := hBzero u hu hune
    have h' : P (some t') * polyTwist (q := Nat.card F) 1 (P (some u))
        - polyTwist (q := Nat.card F) 1 (P (some t')) * P (some u) = 0 := by
      simpa only [hPA] using h
    exact sub_eq_zero.mp h'
  -- the descent along `frobPowHom 1`
  have hσinj : Function.Injective (frobPowHom (K := Ambient F) (q := Nat.card F) 1) := by
    intro x y h
    exact ambPow_injective F 1 (by simpa only [frobPowHom_apply] using h)
  have hρtop' : ρ (some t') = 1 := hρtop
  have hPθt' : (P (some t')).eval (ambTheta F) = 1 := by rw [hPθ (some t'), hρtop']
  have hQne : P (some t') ≠ 0 := by
    intro h
    have h1 : (P (some t')).eval (ambTheta F) = 1 := hPθt'
    have h2 : (P (some t')).eval (ambTheta F)
        = (0 : Polynomial (Ambient F)).eval (ambTheta F) :=
      congrArg (fun p : Polynomial (Ambient F) => p.eval (ambTheta F)) h
    rw [Polynomial.eval_zero] at h2
    rw [h1] at h2
    exact one_ne_zero h2
  have hdes : polyTwist (q := Nat.card F) 1 (P (some u)) * P (some t')
      = P (some u) * polyTwist (q := Nat.card F) 1 (P (some t')) :=
    calc polyTwist (q := Nat.card F) 1 (P (some u)) * P (some t')
        = P (some t') * polyTwist (q := Nat.card F) 1 (P (some u)) := mul_comm _ _
      _ = polyTwist (q := Nat.card F) 1 (P (some t')) * P (some u) := hB0
      _ = P (some u) * polyTwist (q := Nat.card F) 1 (P (some t')) := mul_comm _ _
  obtain ⟨P', Q', hQ'0, hrel3⟩ :=
    Commons.RingTheory.Polynomial.fixed_of_map_mul_eq (frobPowHom (K := Ambient F) (q := Nat.card F) 1) hσinj
      (ambF F) (fun x => (mem_ambF_iff F x).trans (by rw [frobPowHom_apply, pow_one]))
      (P (some u)) (P (some t')) hQne hdes
  -- evaluate at `θ`
  have hθ3 := congrArg (fun p : Polynomial (Ambient F) => p.eval (ambTheta F)) hrel3
  simp only [Polynomial.eval_mul] at hθ3
  rw [Polynomial.eval_map, Polynomial.eval_map] at hθ3
  have hPθu : (P (some u)).eval (ambTheta F) = ρ (some u) := hPθ (some u)
  have hPθt : (P (some t')).eval (ambTheta F) = 1 := by rw [hPθ (some t'), hρtop]
  rw [hPθu, hPθt, mul_one] at hθ3
  -- `P'_u(θ)`, `Q'(θ) ∈ ambK F`
  have hθK : ambTheta F ∈ ambK F := ambTheta_mem_ambK F
  have hcoeffK : ∀ m, ((P'.map (ambF F).subtype).coeff m) ∈ ambK F := by
    intro m
    rw [Polynomial.coeff_map]
    show (((P'.coeff m : ↥(ambF F))) : Ambient F) ∈ ambK F
    obtain ⟨c, hc⟩ := (show (P'.coeff m : Ambient F) ∈ Set.range (ambCoeff F) from by
      rw [range_ambCoeff_eq_ambF]; exact (P'.coeff m).2)
    rw [← hc]
    exact ambCoeff_mem_ambK F c
  have hPK : (P'.map (ambF F).subtype).eval (ambTheta F) ∈ ambK F := by
    rw [Polynomial.eval_eq_sum_range]
    exact Subfield.sum_mem _ fun i _ =>
      Subfield.mul_mem _ (hcoeffK i) (Subfield.pow_mem _ hθK i)
  have hcoeffK' : ∀ m, ((Q'.map (ambF F).subtype).coeff m) ∈ ambK F := by
    intro m
    rw [Polynomial.coeff_map]
    show (((Q'.coeff m : ↥(ambF F))) : Ambient F) ∈ ambK F
    obtain ⟨c, hc⟩ := (show (Q'.coeff m : Ambient F) ∈ Set.range (ambCoeff F) from by
      rw [range_ambCoeff_eq_ambF]; exact (Q'.coeff m).2)
    rw [← hc]
    exact ambCoeff_mem_ambK F c
  have hQK : (Q'.map (ambF F).subtype).eval (ambTheta F) ∈ ambK F := by
    rw [Polynomial.eval_eq_sum_range]
    exact Subfield.sum_mem _ fun i _ =>
      Subfield.mul_mem _ (hcoeffK' i) (Subfield.pow_mem _ hθK i)
  have hQKne : (Q'.map (ambF F).subtype).eval (ambTheta F) ≠ 0 := hQ'ne hQ'0
  have : ρ (some u) = (P'.map (ambF F).subtype).eval (ambTheta F)
      / (Q'.map (ambF F).subtype).eval (ambTheta F) := by
    rw [eq_div_iff hQKne]
    simpa only [Polynomial.eval_map] using hθ3.symm
  rw [this]
  exact Subfield.div_mem _ hPK hQK

end ZagierHoffmanPositiveChar

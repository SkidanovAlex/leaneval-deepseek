import Mathlib
import Submission.Work.BW.bwScale


/-!
# The scaling action on associated primes of the coordinate ring of `(P¹)^{N+1}`

Let `MR N = ℂ[X_{i,0}, X_{i,1}]_{i ≤ N}` and let `scaleEnd N lam` be the ℂ-algebra endomorphism
sending `X_{i,j} ↦ lam i * X_{i,j}`.  For `lam` a tuple of *units* this endomorphism is an
automorphism, with inverse `scaleEnd N (invPt lam)`.

The main result: if an ideal `I` is stable under all the endomorphisms `scaleEnd N lam`
(`lam : Fin (N+1) → ℂ` arbitrary), then every associated prime `p` of the module
`R ⧸ I` is stable under the automorphisms `scaleEnd N lam` for `lam` a tuple of units.
Equivalently, `p` is invariant under the torus action.

The proof: stability of `I` under all scalings makes it stable under the *invertible* scalings
`σ_μ`, so `σ_μ` induces an automorphism of `R ⧸ I`; consequently `σ_μ (p)` is again an associated
prime of `R ⧸ I`.  Since there are only finitely many associated primes, the orbit of `p` under any
one-parameter family of scalings is finite, so some iterate `σ_μ^m p = p` with `1 ≤ m ≤ #Ass`.
The automorphisms `σ_μ` commute with the action, so `σ_μ^{m!} p = p`.  Finally every tuple of units
`lam` has a `k`-th root `μ` for every `k ≥ 1`; taking `k = #Ass !` gives
`σ_lam p = σ_μ^{k} p = p`.
-/

open MvPolynomial

set_option linter.style.haveILetI false

namespace Work.BW

variable {N : ℕ}

/-- `scaleEnd N lam` for a tuple of units, as an algebra equivalence. -/
private noncomputable def scaleAlgEquiv (N : ℕ) (lam : Fin (N + 1) → ℂˣ) : MR N ≃ₐ[ℂ] MR N :=
  AlgEquiv.ofAlgHom (scaleEnd N (fun i => (lam i : ℂ))) (scaleEnd N (invPt lam))
    (scaleEnd_comp_invPt lam) (scaleEnd_invPt_comp lam)

/-- The scaling equivalence acts on ideals through `scaleEnd`. -/
private lemma scaleAlgEquiv_apply_eq (N : ℕ) (lam : Fin (N + 1) → ℂˣ) (I : Ideal (MR N)) :
    Ideal.map (scaleAlgEquiv N lam) I = Ideal.map (scaleEnd N (fun i => (lam i : ℂ))) I := rfl

/-- A scaling-stable ideal is stable under the scaling equivalences. -/
private lemma map_scaleAlgEquiv_eq (I : Ideal (MR N))
    (hσI : ∀ (lam : Fin (N + 1) → ℂ) (r : MR N), r ∈ I → scaleEnd N lam r ∈ I)
    (lam : Fin (N + 1) → ℂˣ) : Ideal.map (scaleAlgEquiv N lam) I = I := by
  rw [scaleAlgEquiv_apply_eq]
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact hσI (fun i => (lam i : ℂ)) r hr
  · intro r hr
    have hx : scaleEnd N (invPt lam) r ∈ I := hσI (invPt lam) r hr
    have h1 : scaleEnd N (fun i => (lam i : ℂ)) (scaleEnd N (invPt lam) r) = r := by
      have h := congrArg (fun (f : MR N →ₐ[ℂ] MR N) => f r) (scaleEnd_comp_invPt lam)
      simpa using h
    rw [← h1]
    exact Ideal.mem_map_of_mem (scaleEnd N (fun i => (lam i : ℂ))) hx

/-- The scaling of `invPt lam` is a left inverse of the scaling of `lam` on ideals. -/
private lemma map_invPt_scaleEnd (lam : Fin (N + 1) → ℂˣ) (p : Ideal (MR N)) :
    Ideal.map (scaleEnd N (invPt lam)) (Ideal.map (scaleEnd N (fun i => (lam i : ℂ))) p) = p := by
  have hcomp : (scaleEnd N (invPt lam)).comp (scaleEnd N (fun i => (lam i : ℂ))) =
      AlgHom.id ℂ (MR N) := by
    rw [scaleEnd_comp, scaleEnd_invPt_mul, scaleEnd_one]
  rw [Ideal.map_mapₐ, hcomp, Ideal.map_idₐ]

/-- The action of the unit scalings on ideals is multiplicative. -/
private lemma map_map_scaleEnd (lam nu : Fin (N + 1) → ℂˣ) (p : Ideal (MR N)) :
    Ideal.map (scaleEnd N (fun i => (lam i : ℂ)))
        (Ideal.map (scaleEnd N (fun i => (nu i : ℂ))) p) =
      Ideal.map (scaleEnd N (fun i => (((lam i) * (nu i) : ℂˣ) : ℂ))) p := by
  have h : (fun i => ((lam i : ℂ) * (nu i : ℂ))) =
      (fun i => (((lam i * nu i) : ℂˣ) : ℂ)) := by
    funext i
    simp
  rw [Ideal.map_mapₐ, scaleEnd_comp, h]

/-- An algebra equivalence fixing `I` preserves the associated primes of `R ⧸ I`. -/
private theorem map_mem_associatedPrimes (I : Ideal (MR N)) (e : MR N ≃ₐ[ℂ] MR N)
    (hI : Ideal.map e I = I) {p : Ideal (MR N)}
    (hp : p ∈ associatedPrimes (MR N) (MR N ⧸ I)) :
    Ideal.map e p ∈ associatedPrimes (MR N) (MR N ⧸ I) := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp ⊢
  obtain ⟨hpprime, x, hpx⟩ := hp
  haveI := hpprime
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨inferInstance, Ideal.Quotient.mk I (e r), ?_⟩
  rw [hpx]
  have hmem : ∀ a : MR N, e a ∈ I ↔ a ∈ I := by
    intro a
    constructor
    · intro ha
      rw [← hI] at ha
      rw [Ideal.mem_map_iff_of_surjective e e.surjective] at ha
      obtain ⟨b, hb, hba⟩ := ha
      have : b = a := e.injective hba
      rwa [← this]
    · intro ha
      rw [← hI]
      exact Ideal.mem_map_of_mem e ha
  have hsmul : ∀ (b x : MR N), b • (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (b * x) := by
    intro b x
    rw [← Ideal.Quotient.mk_eq_mk,
      ← Submodule.Quotient.mk_smul (p := (I : Submodule (MR N) (MR N))) b x]
    simp
  have key : ∀ a : MR N,
      a ∈ Ideal.map e ((⊥ : Submodule (MR N) (MR N ⧸ I)).colon {Ideal.Quotient.mk I r}) ↔
        a * e r ∈ I := by
    intro a
    rw [Ideal.mem_map_iff_of_surjective e e.surjective]
    constructor
    · rintro ⟨b, hb, hba⟩
      rw [Submodule.mem_colon_singleton, hsmul] at hb
      simp only [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hb
      rw [← hba, ← map_mul]
      exact (hmem (b * r)).mpr hb
    · intro ha
      refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
      rw [Submodule.mem_colon_singleton, hsmul, Submodule.mem_bot,
        Ideal.Quotient.eq_zero_iff_mem]
      rw [(hmem (e.symm a * r)).symm]
      rwa [map_mul, e.apply_symm_apply]
  ext a
  rw [key a, Submodule.mem_colon_singleton, hsmul]
  simp only [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]

/-- The scaling of a unit tuple preserves the associated primes of `R ⧸ I`. -/
private lemma scaleEnd_mem_associatedPrimes (I : Ideal (MR N))
    (hσI : ∀ (lam : Fin (N + 1) → ℂ) (r : MR N), r ∈ I → scaleEnd N lam r ∈ I)
    (lam : Fin (N + 1) → ℂˣ) {p : Ideal (MR N)}
    (hp : p ∈ associatedPrimes (MR N) (MR N ⧸ I)) :
    Ideal.map (scaleEnd N (fun i => (lam i : ℂ))) p ∈ associatedPrimes (MR N) (MR N ⧸ I) := by
  have h := map_mem_associatedPrimes I (scaleAlgEquiv N lam) (map_scaleAlgEquiv_eq I hσI lam) hp
  rwa [scaleAlgEquiv_apply_eq] at h

/-- The action of a unit tuple of scalars on ideals. -/
private noncomputable def scaleId (N : ℕ) (nu : Fin (N + 1) → ℂˣ) :
    Ideal (MR N) → Ideal (MR N) :=
  fun q => Ideal.map (scaleEnd N (fun i => (nu i : ℂ))) q

private lemma scaleId_apply (nu : Fin (N + 1) → ℂˣ) (q : Ideal (MR N)) :
    scaleId N nu q = Ideal.map (scaleEnd N (fun i => (nu i : ℂ))) q := rfl

private lemma scaleId_mul (nu nu' : Fin (N + 1) → ℂˣ) (q : Ideal (MR N)) :
    scaleId N (fun i => nu i * nu' i) q = scaleId N nu (scaleId N nu' q) := by
  rw [scaleId_apply, scaleId_apply, scaleId_apply]
  exact (map_map_scaleEnd nu nu' q).symm

private lemma scaleId_one (q : Ideal (MR N)) :
    scaleId N (fun _ : Fin (N + 1) => 1) q = q := by
  rw [scaleId_apply]
  have h : (fun _ : Fin (N + 1) => (((1 : ℂˣ)) : ℂ)) = (fun _ => (1 : ℂ)) := by
    funext i
    simp
  rw [h, scaleEnd_one, Ideal.map_idₐ]

private lemma scaleId_injective (nu : Fin (N + 1) → ℂˣ) : Function.Injective (scaleId N nu) := by
  intro q q' h
  have h1 := congrArg (fun r => Ideal.map (scaleEnd N (invPt nu)) r) h
  rw [scaleId_apply, scaleId_apply] at h1
  rwa [map_invPt_scaleEnd, map_invPt_scaleEnd] at h1

private lemma scaleId_pow (nu : Fin (N + 1) → ℂˣ) (k : ℕ) (q : Ideal (MR N)) :
    scaleId N (fun i => nu i ^ k) q = (scaleId N nu)^[k] q := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply]
    rw [show (fun i => nu i ^ 0) = (fun _ : Fin (N + 1) => 1) from
      funext (fun i => pow_zero (nu i))]
    exact scaleId_one q
  | succ k ih =>
    rw [show (fun i => nu i ^ (k + 1)) = (fun i => nu i * nu i ^ k) from
      funext (fun i => pow_succ' (nu i) k)]
    rw [scaleId_mul nu (fun i => nu i ^ k) q, ih, Function.iterate_succ_apply']

/-- Every tuple of units has a coordinatewise `k`-th root, for `k ≥ 1`. -/
private lemma exists_root_units (lam : Fin (N + 1) → ℂˣ) (k : ℕ) (hk : 0 < k) :
    ∃ mu : Fin (N + 1) → ℂˣ, ∀ i, mu i ^ k = lam i := by
  have hex : ∀ i, ∃ w : ℂˣ, w ^ k = lam i := by
    intro i
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((lam i : ℂ)) hk
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_pow hk.ne'] at hz
      exact (lam i).ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  exact ⟨fun i => (hex i).choose, fun i => (hex i).choose_spec⟩

theorem map_scaleEnd_eq_self {N : ℕ} (I : Ideal (MR N))
    (hσI : ∀ (lam : Fin (N + 1) → ℂ) (r : MR N), r ∈ I → scaleEnd N lam r ∈ I)
    (p : Ideal (MR N)) (hp : p ∈ associatedPrimes (MR N) (MR N ⧸ I)) :
    ∀ lam : Fin (N + 1) → ℂˣ,
      Ideal.map (scaleEnd N (fun i => (lam i : ℂ))) p = p := by
  classical
  intro lam
  -- the finite set of associated primes of `R ⧸ I`
  set s : Finset (Ideal (MR N)) := (associatedPrimes.finite (MR N) (MR N ⧸ I)).toFinset with hs
  have hmem_s : ∀ q : Ideal (MR N), q ∈ s ↔ q ∈ associatedPrimes (MR N) (MR N ⧸ I) := by
    intro q
    rw [hs, Set.Finite.mem_toFinset]
  have hps : p ∈ s := (hmem_s p).mpr hp
  -- the scaling action maps `s` into itself
  have hstep : ∀ (nu : Fin (N + 1) → ℂˣ) (q : Ideal (MR N)), q ∈ s → scaleId N nu q ∈ s := by
    intro nu q hq
    rw [hmem_s] at hq ⊢
    rw [scaleId_apply]
    exact scaleEnd_mem_associatedPrimes I hσI nu hq
  have hiter_mem : ∀ (nu : Fin (N + 1) → ℂˣ) (n : ℕ), (scaleId N nu)^[n] p ∈ s := by
    intro nu n
    induction n with
    | zero => simpa using hps
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hstep nu _ ih
  -- pigeonhole: for every `nu` some positive power at most `#s` fixes `p`
  have key : ∀ nu : Fin (N + 1) → ℂˣ, ∃ m, 0 < m ∧ m ≤ s.card ∧ (scaleId N nu)^[m] p = p := by
    intro nu
    obtain ⟨a, ha, b, hb, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := Finset.range (s.card + 1)) (t := s) (by simp)
        (f := fun n => (scaleId N nu)^[n] p)
        (fun n _ => hiter_mem nu n)
    rw [Finset.mem_range] at ha hb
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨b - a, Nat.sub_pos_of_lt hlt, by omega,
        Function.iterate_cancel (scaleId_injective nu) heq.symm⟩
    · exact ⟨a - b, Nat.sub_pos_of_lt hlt, by omega,
        Function.iterate_cancel (scaleId_injective nu) heq⟩
  -- hence the factorial power fixes `p`
  have key2 : ∀ nu : Fin (N + 1) → ℂˣ, (scaleId N nu)^[(s.card).factorial] p = p := by
    intro nu
    obtain ⟨m, hmpos, hmle, hm⟩ := key nu
    have haux : ∀ r : ℕ, ((scaleId N nu)^[m])^[r] p = p := by
      intro r
      induction r with
      | zero => rfl
      | succ r ih => rw [Function.iterate_succ_apply', ih, hm]
    obtain ⟨r, hr⟩ := Nat.dvd_factorial hmpos hmle
    rw [hr, Function.iterate_mul]
    exact haux r
  -- root extraction and conclusion
  obtain ⟨mu, hmu⟩ := exists_root_units lam (s.card).factorial (Nat.factorial_pos _)
  have hfinal : scaleId N (fun i => mu i ^ (s.card).factorial) p = p := by
    rw [scaleId_pow]
    exact key2 mu
  rw [show (fun i => mu i ^ (s.card).factorial) = lam from funext hmu] at hfinal
  simpa only [scaleId_apply] using hfinal

end Work.BW

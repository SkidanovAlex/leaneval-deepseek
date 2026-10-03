import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Grading

open scoped TensorProduct

open Work.ORTorsion

open Work.ORTorsion.LaurentBase

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]
  {gen : G →* Uˣ} {D : Subgroup G → Subalgebra K U} {H : Subgroup G} {φ : H →* Multiplicative ℤ}

/-! ## Auxiliary lemmas

The target identity is the statement that the diagonal action of `h ∈ H` on `V ⊗ R` maps the
"degree zero" part `V ⊗ D(N)` into the shift by `deg φ h` of itself.  The mathematical content is
the round-trip identity in `U`: for `d ∈ D(N)` there is `d' ∈ D(N)` with
`gen h * d = d' * u ^ (deg φ h)`, where `u = gen s`.  Writing `h = a * s ^ b` with `b = deg φ h`
and `a ∈ N`, this is `gen h = gen a * u ^ b` together with the fact that conjugation by `u ^ b`
preserves `D(N)` (which holds because `s ^ b` normalises `N = ker φ`). -/

/-- An element of `H` which lies in `N = ker φ` is killed by `φ`. -/
private lemma mem_ker_of_mem_N (Lb : LaurentBase K U G gen D H φ) {y : G} (hy : y ∈ Lb.N) :
    φ ⟨y, Lb.N_le_H hy⟩ = 1 := by
  have hy' : y ∈ φ.ker.map H.subtype := by rwa [Lb.hN] at hy
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
  have : z = ⟨y, Lb.N_le_H hy⟩ := Subtype.ext hzy
  rw [← this]
  simpa using hz

/-- Conjugation by `s ^ b` (which lies in `H`) preserves `N = ker φ`. -/
private lemma N_map_conj_le (Lb : LaurentBase K U G gen D H φ) (b : ℤ) :
    Lb.N.map (MulAut.conj ((Lb.s : G) ^ b)) ≤ Lb.N := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
  rw [← hxy]
  change ((Lb.s : G) ^ b * y * ((Lb.s : G) ^ b)⁻¹) ∈ Lb.N
  have hgH : ((Lb.s : G) ^ b) ∈ H := H.zpow_mem Lb.s.2 b
  have hyH : y ∈ H := Lb.N_le_H hy
  have hker : (⟨(Lb.s : G) ^ b, hgH⟩ * ⟨y, hyH⟩ * (⟨(Lb.s : G) ^ b, hgH⟩)⁻¹ : H) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv]
    rw [show φ ⟨y, hyH⟩ = 1 from mem_ker_of_mem_N Lb hy]
    simp
  have hmem := Lb.mem_N_of_mem_ker hker
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hmem

variable (L : TorsionData K G U)

/-- Conjugation by a power of `u = gen s` preserves `D(N)`: this is the conjugation axiom (I2)
of `TorsionData` together with the fact that `s ^ b` normalises `N = ker φ`. -/
private lemma zpow_conj_mem (Lb : LaurentBase K U G L.gen L.D H φ) (b : ℤ) {d : U}
    (hd : d ∈ L.D Lb.N) :
    (↑((L.gen (Lb.s : G)) ^ b) : U) * d * ↑(((L.gen (Lb.s : G)) ^ b)⁻¹) ∈ L.D Lb.N := by
  have h1 := L.conjugation ((Lb.s : G) ^ b) Lb.N d hd
  have hgen : (L.gen ((Lb.s : G) ^ b) : U) = ↑((L.gen (Lb.s : G)) ^ b : Uˣ) := by rw [map_zpow]
  have hinv : (↑((L.gen ((Lb.s : G) ^ b))⁻¹) : U) = ↑(((L.gen (Lb.s : G)) ^ b)⁻¹ : Uˣ) := by
    rw [map_zpow]
  rw [hgen, hinv] at h1
  exact L.D_mono (N_map_conj_le Lb b) h1

/-- **The round-trip identity.**  For `d ∈ D(N)` there is `d' ∈ D(N)` with
`gen h * d = d' * u ^ (deg φ h)`, where `u = gen s`. -/
private lemma exists_genD_mul (Lb : LaurentBase K U G L.gen L.D H φ) (h : H)
    (d : ↥(L.D Lb.N)) :
    ∃ d' : ↥(L.D Lb.N),
      (L.gen (h : G) : U) * (d : U) = (d' : U) * ↑((L.gen (Lb.s : G)) ^ (deg φ h) : Uˣ) := by
  set a : H := h * Lb.s ^ (-(deg φ h)) with ha
  have ha_mem : (a : G) ∈ Lb.N := by
    rw [ha]
    exact Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow (deg_apply φ h))
  have hgenA : (L.gen (a : G) : U) ∈ L.D Lb.N := L.gen_mem Lb.N ⟨(a : G), ha_mem⟩
  have hconj : (↑((L.gen (Lb.s : G)) ^ (deg φ h)) : U) * (d : U) *
      ↑(((L.gen (Lb.s : G)) ^ (deg φ h))⁻¹) ∈ L.D Lb.N :=
    zpow_conj_mem L Lb (deg φ h) d.2
  refine ⟨⟨(L.gen (a : G) : U) * (↑((L.gen (Lb.s : G)) ^ (deg φ h)) * (d : U) *
      ↑(((L.gen (Lb.s : G)) ^ (deg φ h))⁻¹)), mul_mem hgenA hconj⟩, ?_⟩
  have h_eq : h = a * Lb.s ^ (deg φ h) := by rw [ha]; group
  have hG : (h : G) = (a : G) * (Lb.s : G) ^ (deg φ h) := by
    have := congrArg (fun x : H => (x : G)) h_eq
    simpa only [Subgroup.coe_mul, Subgroup.coe_zpow] using this
  have hgen_eq : L.gen (h : G) = L.gen (a : G) * (L.gen (Lb.s : G)) ^ (deg φ h) := by
    rw [hG, map_mul, map_zpow]
  have hgenU : (L.gen (h : G) : U) = (L.gen (a : G) : U) *
      ↑((L.gen (Lb.s : G)) ^ (deg φ h) : Uˣ) := by
    rw [hgen_eq, Units.val_mul]
  rw [hgenU]
  have hunit : (↑(((L.gen (Lb.s : G)) ^ (deg φ h))⁻¹) : U) *
      (↑((L.gen (Lb.s : G)) ^ (deg φ h)) : U) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [mul_assoc]
  rw [hunit, mul_one]

/-- The round-trip identity transported to `R`. -/
private lemma genR_mul_eq_rightMulU (Lb : LaurentBase K U G L.gen L.D H φ) (h : H)
    (d d' : ↥(L.D Lb.N))
    (hd' : (L.gen (h : G) : U) * (d : U) = (d' : U) * ↑((L.gen (Lb.s : G)) ^ (deg φ h) : Uˣ)) :
    Lb.genR h * Subalgebra.inclusion Lb.DN_le_R d
      = Lb.rightMulU (deg φ h) (Subalgebra.inclusion Lb.DN_le_R d') := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Lb.rightMulU_coe]
  show (L.gen (h : G) : U) * (d : U) = (d' : U) * ↑((L.gen (Lb.s : G)) ^ (deg φ h) : Uˣ)
  exact hd'

/-- The diagonal action of `single h 1 ∈ K[H]` is the diagonal operator attached to `h`. -/
private lemma single_smul_eq_diagElem {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (Lb : LaurentBase K U G L.gen L.D H φ) (h : H) (w : V ⊗[K] ↥Lb.R) :
    (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H) • w
      = diagElem (K:=K) (V:=V) H.subtype Lb.genR h w := by
  change diagRingHom (K:=K) (V:=V) H.subtype Lb.genR (MonoidAlgebra.single h (1 : K)) w
      = diagElem (K:=K) (V:=V) H.subtype Lb.genR h w
  rw [diagRingHom_single]
  rfl

/-- The diagonal action of `single h 1` on a simple tensor of `V ⊗ D(N)`. -/
private lemma single_smul_inclDN_tmul {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (Lb : LaurentBase K U G L.gen L.D H φ) (h : H) (v : V) (d : ↥(L.D Lb.N)) :
    (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H) • (inclDN Lb (v ⊗ₜ[K] d))
      = gAct (K:=K) (h : G) v ⊗ₜ[K] (Lb.genR h * Subalgebra.inclusion Lb.DN_le_R d) := by
  rw [LaurentBase.inclDN_tmul]
  rw [single_smul_eq_diagElem L Lb h]
  rw [diagElem_apply_tmul]
  rfl

/-- `Tm` on a simple tensor of `V ⊗ D(N)` (embedded into `V ⊗ R`). -/
private lemma Tm_inclDN_tmul {V : Type*} [AddCommGroup V] [Module K V]
    (Lb : LaurentBase K U G L.gen L.D H φ) (k : ℤ) (w : V) (d : ↥(L.D Lb.N)) :
    Tm Lb k (inclDN Lb (w ⊗ₜ[K] d))
      = w ⊗ₜ[K] (Lb.rightMulU k (Subalgebra.inclusion Lb.DN_le_R d)) := by
  rw [LaurentBase.inclDN_tmul, LaurentBase.Tm_tmul]
  rfl

theorem exists_single_smul_mem_range {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (h : H) (z : V ⊗[K] ↥(L.D Lb.N)) :
    ∃ z' : V ⊗[K] ↥(L.D Lb.N),
      (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H) • (inclDN Lb z)
        = Tm Lb (deg φ h) (inclDN Lb z') := by
  have key : ∀ z : V ⊗[K] ↥(L.D Lb.N), ∃ z' : V ⊗[K] ↥(L.D Lb.N),
      (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H) • (inclDN Lb z)
        = Tm Lb (deg φ h) (inclDN Lb z') := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul v d =>
        obtain ⟨d', hd'⟩ := exists_genD_mul L Lb h d
        exact ⟨gAct (K:=K) (h:G) v ⊗ₜ[K] d', by
          rw [single_smul_inclDN_tmul L Lb h v d,
            Tm_inclDN_tmul L Lb (deg φ h) (gAct (K:=K) (h:G) v) d',
            genR_mul_eq_rightMulU L Lb h d d' hd']⟩
    | add x y ihx ihy =>
        obtain ⟨x', hx'⟩ := ihx
        obtain ⟨y', hy'⟩ := ihy
        exact ⟨x' + y', by simp only [map_add, smul_add, hx', hy']⟩
  exact key z

end Work.ORTorsion.Grading

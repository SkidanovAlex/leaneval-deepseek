import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Galois.decomposition
import Submission.Work.AUTL2.Aut.centralizer
import Submission.Work.AUTL2.Aut.images
import Submission.Work.AUTL2.Aut.pglIndex
import Submission.Work.AUTL2.Main.realize
import Submission.Work.AUTL2.Main.a5odd

open scoped MatrixGroups

namespace Work.AUTL2.Main

variable {p k : ℕ} [Fact p.Prime]

/-- `DihOrCycSylow` is invariant under group isomorphisms. -/
private theorem dihOrCycSylow_of_mulEquiv {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (e : G ≃* H) (h : Work.GW2.DihOrCycSylow G) :
    Work.GW2.DihOrCycSylow H := by
  intro Q
  let P : Sylow 2 G := Q.comapOfInjective (e : G →* H) e.injective
    (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
  have hx : ∀ x : ↥P, e (x : G) ∈ (Q : Subgroup H) := fun x => x.2
  have iso : ↥P ≃* ↥Q :=
    { toFun := fun x => ⟨e (x : G), hx x⟩
      invFun := fun y => ⟨e.symm (y : H), by
        show e (e.symm (y : H)) ∈ (Q : Subgroup H)
        rw [MulEquiv.apply_symm_apply]; exact y.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show e ((a * b : ↥P) : G) = e (a : G) * e (b : G)
        rw [show ((a * b : ↥P) : G) = (a : G) * (b : G) from rfl, map_mul]) }
  rcases h P with hcyc | ⟨n, ⟨en⟩⟩
  · left
    haveI : IsCyclic ↥P := hcyc
    exact isCyclic_of_surjective iso.toMonoidHom iso.surjective
  · exact Or.inr ⟨n, ⟨iso.symm.trans en⟩⟩

theorem autL2 (p k : ℕ) [Fact p.Prime]
    (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q)
    (e : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))
    (hp : Odd p) (hq : 5 ≤ p ^ k) (hL : L.Normal)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) (hdih : Work.GW2.DihOrCycSylow Q) :
    ∃ M : Subgroup Q, M.Normal ∧ L ≤ M ∧ Odd M.index ∧
      (Nonempty (↥M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∨
        Nonempty (↥M ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))) := by
  classical
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  haveI : DecidableEq (GaloisField p k) := Classical.decEq _
  letI : L.Normal := hL
  -- ## The conjugation action of `Q` on `PSL(2,q)` through `e`
  let conjh : Q →* MulAut ↥L := MulAut.conjNormal
  let γ : Q →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    (MulAut.congr e).toMonoidHom.comp conjh
  have conjh_apply : ∀ (q : Q) (x : ↥L),
      conjh q x = ⟨(q * (x : Q) * q⁻¹ : Q), hL.conj_mem x x.2 q⟩ := by
    intro q x
    exact Subtype.ext (MulAut.conjNormal_apply q x)
  have γ_apply : ∀ (q : Q) (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)),
      γ q z = e (conjh q (e.symm z)) := fun q z => rfl
  have γ_apply_e : ∀ (q : Q) (x : ↥L), γ q (e x) = e (conjh q x) := by
    intro q x
    rw [γ_apply, MulEquiv.symm_apply_apply]
  have γ_mul_general : ∀ (q : Q) (x : ↥L),
      γ q (e x) = e ⟨(q * (x : Q) * q⁻¹ : Q), hL.conj_mem x x.2 q⟩ := by
    intro q x
    rw [γ_apply_e, conjh_apply]
  have γ_mul : ∀ (x : ↥L) (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)),
      γ x z = e x * z * (e x)⁻¹ := by
    intro x z
    have hx : conjh x (e.symm z) = x * e.symm z * x⁻¹ := by
      rw [conjh_apply]
      exact Subtype.ext rfl
    rw [γ_apply, hx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  -- ## Choice of a realizing permutation `πf q ∈ PΓL(2,q)` for each `q`
  let πf : Q → Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) :=
    fun q => Classical.choose (realize p k hp hq (γ q))
  have πf_mem : ∀ q, πf q ∈ Work.AUTL2.pgammaL (GaloisField p k) :=
    fun q => (Classical.choose_spec (realize p k hp hq (γ q))).1
  have πf_conj : ∀ (q : Q)
      (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)),
      πf q * Work.AUTL2.pslHom (GaloisField p k) x * (πf q)⁻¹ =
        Work.AUTL2.pslHom (GaloisField p k) (γ q x) :=
    fun q => (Classical.choose_spec (realize p k hp hq (γ q))).2
  -- ## Uniqueness of the realizer (the centralizer of `pslImage` is trivial)
  have uniq : ∀ (q : Q) (π : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))),
      (∀ x, π * Work.AUTL2.pslHom (GaloisField p k) x * π⁻¹ =
        Work.AUTL2.pslHom (GaloisField p k) (γ q x)) → π = πf q := by
    intro q π hπ
    have hconj : ∀ x, (π⁻¹ * πf q) * Work.AUTL2.pslHom (GaloisField p k) x *
        (π⁻¹ * πf q)⁻¹ = Work.AUTL2.pslHom (GaloisField p k) x := by
      intro x
      calc (π⁻¹ * πf q) * Work.AUTL2.pslHom (GaloisField p k) x * (π⁻¹ * πf q)⁻¹
          = π⁻¹ * (πf q * Work.AUTL2.pslHom (GaloisField p k) x * (πf q)⁻¹) * π := by group
        _ = π⁻¹ * Work.AUTL2.pslHom (GaloisField p k) (γ q x) * π := by rw [πf_conj q x]
        _ = π⁻¹ * (π * Work.AUTL2.pslHom (GaloisField p k) x * π⁻¹) * π := by rw [← hπ x]
        _ = Work.AUTL2.pslHom (GaloisField p k) x := by group
    have hmem : π⁻¹ * πf q ∈ Subgroup.centralizer
        (Work.AUTL2.pslImage (GaloisField p k) :
          Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨x, rfl⟩
      calc Work.AUTL2.pslHom (GaloisField p k) x * (π⁻¹ * πf q)
          = ((π⁻¹ * πf q) * Work.AUTL2.pslHom (GaloisField p k) x *
              (π⁻¹ * πf q)⁻¹) * (π⁻¹ * πf q) := by rw [hconj x]
        _ = (π⁻¹ * πf q) * Work.AUTL2.pslHom (GaloisField p k) x := by group
    have hbot : π⁻¹ * πf q ∈
        (⊥ : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) := by
      rwa [← Work.AUTL2.Aut.centralizer p k hp hq]
    have h1 : π⁻¹ * πf q = 1 := Subgroup.mem_bot.mp hbot
    calc π = π * (π⁻¹ * πf q) := by rw [h1, mul_one]
      _ = πf q := by group
  -- ## `Φ : Q →* Sym(ℙ¹)`
  have Φ_one : πf 1 = 1 := by
    refine (uniq 1 1 ?_).symm
    intro x
    have h1 : γ 1 x = x := by
      rw [γ_apply, map_one]
      simp
    rw [one_mul, inv_one, mul_one, h1]
  have Φ_mul : ∀ a b : Q, πf (a * b) = πf a * πf b := by
    intro a b
    refine (uniq (a * b) (πf a * πf b) ?_).symm
    intro x
    rw [map_mul, MulAut.mul_apply]
    calc πf a * πf b * Work.AUTL2.pslHom (GaloisField p k) x * (πf a * πf b)⁻¹
        = πf a * (πf b * Work.AUTL2.pslHom (GaloisField p k) x * (πf b)⁻¹) *
            (πf a)⁻¹ := by group
      _ = πf a * Work.AUTL2.pslHom (GaloisField p k) (γ b x) * (πf a)⁻¹ := by
            rw [πf_conj b x]
      _ = Work.AUTL2.pslHom (GaloisField p k) (γ a (γ b x)) := πf_conj a (γ b x)
  let Φ : Q →* Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) :=
    { toFun := πf, map_one' := Φ_one, map_mul' := Φ_mul }
  have Φ_inj : Function.Injective Φ := by
    intro a b hab
    have h1 : Φ (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab]
      simp
    have h2 : ∀ x : ↥L, (a⁻¹ * b) * (x : Q) * (a⁻¹ * b)⁻¹ = (x : Q) := by
      intro x
      have h3 : γ (a⁻¹ * b) (e x) = e x := by
        have h := πf_conj (a⁻¹ * b) (e x)
        rw [show πf (a⁻¹ * b) = 1 from h1] at h
        simp only [one_mul, inv_one, mul_one] at h
        exact Work.AUTL2.Aut.pslHomInjective _ h.symm
      have h4 : (⟨((a⁻¹ * b) * (x : Q) * (a⁻¹ * b)⁻¹ : Q),
          hL.conj_mem x x.2 (a⁻¹ * b)⟩ : ↥L) = x := by
        apply e.injective
        rw [← γ_mul_general (a⁻¹ * b) x, h3]
      exact Subtype.ext_iff.mp h4
    have hmem : a⁻¹ * b ∈ Subgroup.centralizer (L : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h5 := h2 ⟨x, hx⟩
      calc x * (a⁻¹ * b) = ((a⁻¹ * b) * x * (a⁻¹ * b)⁻¹) * (a⁻¹ * b) := by rw [h5]
        _ = (a⁻¹ * b) * x := by group
    have h6 : a⁻¹ * b = 1 := by
      rw [hC] at hmem
      exact Subgroup.mem_bot.mp hmem
    calc a = a * (a⁻¹ * b) := by rw [h6, mul_one]
      _ = b := by group
  -- ## The range `Q̄ = Φ(Q)`
  set Qbar : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) := Φ.range with hQbar
  have hQbar_le : Qbar ≤ Work.AUTL2.pgammaL (GaloisField p k) := by
    rintro _ ⟨q, rfl⟩
    exact πf_mem q
  have hpgammaLN : Work.AUTL2.pgammaL (GaloisField p k) ≤
      Subgroup.normalizer (Work.AUTL2.pglImage (GaloisField p k) : Set _) := by
    rw [Work.AUTL2.pgammaL]
    refine sup_le ?_ (Work.AUTL2.Galois.galSub_le_normalizer_pglImage _)
    exact Subgroup.le_normalizer_iff.mpr (fun a ha b hb => mul_mem (mul_mem ha hb) (inv_mem ha))
  -- ## `pslImage ≤ Q̄` : `Φ` fixes the copy of `L`
  have Φ_L : ∀ x : ↥L, Φ x = Work.AUTL2.pslHom (GaloisField p k) (e x) := by
    intro x
    refine (uniq x (Work.AUTL2.pslHom (GaloisField p k) (e x)) ?_).symm
    intro y
    rw [γ_mul x y, ← map_mul, ← map_inv, ← map_mul]
  have hpsl_le_Qbar : Work.AUTL2.pslImage (GaloisField p k) ≤ Qbar := by
    rintro u ⟨z, rfl⟩
    exact ⟨e.symm z, by rw [Φ_L, MulEquiv.apply_symm_apply]⟩
  have hdih_Qbar : Work.GW2.DihOrCycSylow ↥Qbar :=
    dihOrCycSylow_of_mulEquiv (MonoidHom.ofInjective Φ_inj) hdih
  -- ## Step A5
  have hA5 : Odd ((Qbar ⊓ Work.AUTL2.pglImage (GaloisField p k)).relIndex Qbar) :=
    a5odd p k hp hq Qbar hQbar_le hpsl_le_Qbar hdih_Qbar
  -- ## `M̄ = Q̄ ⊓ PGL(2,q)` is `PSL(2,q)` or `PGL(2,q)`
  set Mbar : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) :=
    Qbar ⊓ Work.AUTL2.pglImage (GaloisField p k) with hMbar
  have hpsl_le_Mbar : Work.AUTL2.pslImage (GaloisField p k) ≤ Mbar :=
    le_inf hpsl_le_Qbar (Work.AUTL2.pslImage_le_pglImage _)
  have hMbar_le_pgl : Mbar ≤ Work.AUTL2.pglImage (GaloisField p k) := inf_le_right
  have hMbar_eq : Mbar = Work.AUTL2.pslImage (GaloisField p k) ∨
      Mbar = Work.AUTL2.pglImage (GaloisField p k) := by
    have hrel : (Work.AUTL2.pslImage (GaloisField p k)).relIndex Mbar *
        Mbar.relIndex (Work.AUTL2.pglImage (GaloisField p k)) = 2 := by
      rw [← Work.AUTL2.Aut.pglIndex p k hp hq]
      exact Subgroup.relIndex_mul_relIndex _ _ _ hpsl_le_Mbar hMbar_le_pgl
    have hdvd : (Work.AUTL2.pslImage (GaloisField p k)).relIndex Mbar ∣ 2 := ⟨_, hrel.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · left
      exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hpsl_le_Mbar
    · right
      have hb : Mbar.relIndex (Work.AUTL2.pglImage (GaloisField p k)) = 1 := by
        rw [h1, mul_comm] at hrel
        simpa using hrel
      exact le_antisymm hMbar_le_pgl (Subgroup.relIndex_eq_one.mp hb)
  -- ## The subgroup `M = Φ⁻¹(M̄) ⊆ Q`
  have hnorm : (Subgroup.comap Φ Mbar).Normal := by
    refine Subgroup.Normal.mk (fun n hn g => ?_)
    rw [Subgroup.mem_comap] at hn ⊢
    have hconj : Φ g * Φ n * (Φ g)⁻¹ ∈ Mbar := by
      refine Subgroup.mem_inf.mpr ⟨⟨g * n * g⁻¹, ?_⟩, ?_⟩
      · rw [map_mul, map_mul, map_inv]
      · exact (Subgroup.mem_normalizer_iff.mp (hpgammaLN (πf_mem g)) (Φ n)).mp
          (Subgroup.mem_inf.mp hn).2
    rwa [map_mul, map_mul, map_inv]
  have hL_le_M : L ≤ Subgroup.comap Φ Mbar := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [show Φ x = Work.AUTL2.pslHom (GaloisField p k) (e ⟨x, hx⟩) from
      Φ_L ⟨x, hx⟩]
    exact Subgroup.mem_inf.mpr ⟨hpsl_le_Qbar ⟨_, rfl⟩, Work.AUTL2.pslImage_le_pglImage _ ⟨_, rfl⟩⟩
  have hindex : (Subgroup.comap Φ Mbar).index = Mbar.relIndex Φ.range :=
    Subgroup.index_comap Mbar Φ
  have hodd : Odd (Subgroup.comap Φ Mbar).index := by
    rw [hindex]
    exact hA5
  -- ## The isomorphism type of `M`
  have hiso : ↥(Subgroup.comap Φ Mbar) ≃* ↥Mbar := by
    have hmem : ∀ x : ↥(Subgroup.comap Φ Mbar),
        Φ (x : Q) ∈ Mbar := fun x => Subgroup.mem_comap.mp x.2
    let ψ : ↥(Subgroup.comap Φ Mbar) →* ↥Mbar :=
      (Φ.comp (Subgroup.subtype (Subgroup.comap Φ Mbar))).codRestrict Mbar hmem
    have hψ_inj : Function.Injective ψ := by
      intro a b hab
      have h1 : Φ (a : Q) = Φ (b : Q) := Subtype.ext_iff.mp hab
      exact Subtype.ext (Φ_inj h1)
    have hψ_surj : Function.Surjective ψ := by
      intro y
      have hy : (y : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) ∈ Φ.range :=
        (inf_le_left : Mbar ≤ Φ.range) y.2
      rw [MonoidHom.mem_range] at hy
      obtain ⟨q, hq⟩ := hy
      refine ⟨⟨q, ?_⟩, Subtype.ext hq⟩
      rw [Subgroup.mem_comap, hq]
      exact y.2
    exact MulEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩
  refine ⟨Subgroup.comap Φ Mbar, hnorm, hL_le_M, hodd, ?_⟩
  rcases hMbar_eq with hEq | hEq
  · left
    obtain ⟨φ⟩ := (Work.AUTL2.Aut.images p k hp hq).1
    exact ⟨hiso.trans (hEq.symm ▸ φ)⟩
  · right
    obtain ⟨φ⟩ := (Work.AUTL2.Aut.images p k hp hq).2
    exact ⟨hiso.trans (hEq.symm ▸ φ)⟩

end Work.AUTL2.Main
